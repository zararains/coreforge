// github-core-clone-01 entry: a standalone GitHub-compatible git forge.
// One process, standard library only, no git binary. Serves git smart HTTP
// (upload-pack protocol v2, receive-pack v0), REST v3 under /api/v3,
// GraphQL v4 at /api/graphql and MCP at /mcp, all over one in-memory store.
import http from 'node:http';
import crypto from 'node:crypto';
import zlib from 'node:zlib';

// ---------------------------------------------------------------------------
// Trial environment: every timestamp the forge emits derives from
// MAKEFUN_TRIAL_NOW; nothing reads the wall clock into a response.
function parseNow(value) {
  if (!value) return Date.UTC(2025, 0, 1);
  const text = String(value).trim();
  if (/^\d+$/.test(text)) {
    const n = Number(text);
    return n < 1e12 ? n * 1000 : n;
  }
  const parsed = Date.parse(text);
  return Number.isNaN(parsed) ? Date.UTC(2025, 0, 1) : parsed;
}
const NOW_MS = parseNow(process.env.MAKEFUN_TRIAL_NOW);
const NOW_ISO = new Date(NOW_MS).toISOString().replace(/\.\d+Z$/, 'Z');
const NOW_EPOCH = Math.floor(NOW_MS / 1000);
const TOKEN = process.env.MAKEFUN_SHOP_TOKEN || '';
const ENV_URL = (process.env.MAKEFUN_ENV_URL || '').replace(/\/+$/, '');

const VIEWER = { login: 'adaiversen', id: 1000, name: 'ada iversen', email: 'adaiversen@example.invalid' };
const IDENT = `${VIEWER.name} <${VIEWER.email}> ${NOW_EPOCH} +0000`;
const ZERO = '0'.repeat(40);

// ---------------------------------------------------------------------------
// Store
let nextRepoId = 1;
let nextEntryId = 1; // issues and pull requests, global (GraphQL/REST ids)
let nextCommentId = 1;
let requestSeq = 0;
const repos = new Map(); // "owner/name" -> repo

function newRepo(owner, name, description, isPrivate, defaultBranch) {
  return {
    id: nextRepoId++,
    owner,
    name,
    description: description || '',
    private: isPrivate !== false,
    defaultBranch: defaultBranch || 'main',
    objects: new Map(), // sha -> [type, Buffer]
    refs: new Map(), // full ref name -> sha
    labels: new Map(), // name -> {id, name, color, description}
    entries: new Map(), // number -> issue/pull record
    nextNumber: 1,
    seq: 0,
    storeVersion: 0, // bumps whenever a new object lands in the store
    packCache: new Map(), // fetchPack results, keyed by storeVersion + request
    refsVersion: 0, // bumps whenever a ref is created, moved or deleted
    lsRefsCache: new Map(), // ls-refs reply bytes, keyed by versions + args
    fetchCache: new Map(), // upload-pack reply bytes, keyed by storeVersion + request
  };
}
function getRepo(owner, name) {
  return repos.get(`${owner}/${name}`) || null;
}

// ---------------------------------------------------------------------------
// Git object model
const TYPE_NAMES = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };
const TYPE_CODES = { commit: 1, tree: 2, blob: 3, tag: 4 };

function oidOf(type, data) {
  const hash = crypto.createHash('sha1');
  hash.update(`${type} ${data.length}\0`);
  hash.update(data);
  return hash.digest('hex');
}
function storeObject(repo, type, data) {
  const sha = oidOf(type, data);
  if (!repo.objects.has(sha)) {
    repo.objects.set(sha, [type, data]);
    repo.storeVersion += 1;
  }
  return sha;
}
function getObject(repo, sha) {
  return repo.objects.get(sha) || null;
}

function parseCommit(data) {
  const text = data.toString('utf8');
  const split = text.indexOf('\n\n');
  const head = split === -1 ? text : text.slice(0, split);
  const message = split === -1 ? '' : text.slice(split + 2);
  let tree = null;
  const parents = [];
  let author = '';
  let committer = '';
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) author = line.slice(7);
    else if (line.startsWith('committer ')) committer = line.slice(10);
  }
  return { tree, parents, message, author, committer };
}
function buildCommit(tree, parents, message) {
  let head = `tree ${tree}\n`;
  for (const parent of parents) head += `parent ${parent}\n`;
  head += `author ${IDENT}\ncommitter ${IDENT}\n\n`;
  return Buffer.from(head + (message || ''), 'utf8');
}
function parseTag(data) {
  const text = data.toString('utf8');
  let object = null;
  let type = null;
  for (const line of text.split('\n')) {
    if (line.startsWith('object ')) object = line.slice(7).trim();
    else if (line.startsWith('type ')) type = line.slice(5).trim();
    else if (line === '') break;
  }
  return { object, type };
}
function parseTree(data) {
  const entries = [];
  let pos = 0;
  while (pos < data.length) {
    const space = data.indexOf(0x20, pos);
    const mode = data.subarray(pos, space).toString('ascii');
    const nul = data.indexOf(0x00, space + 1);
    const name = data.subarray(space + 1, nul).toString('utf8');
    const oid = data.subarray(nul + 1, nul + 21).toString('hex');
    entries.push({ mode, name, oid });
    pos = nul + 21;
  }
  return entries;
}
function buildTree(entries) {
  const sorted = [...entries].sort((a, b) => {
    const ka = a.mode === '40000' ? `${a.name}/` : a.name;
    const kb = b.mode === '40000' ? `${b.name}/` : b.name;
    return ka < kb ? -1 : ka > kb ? 1 : 0;
  });
  const parts = [];
  for (const entry of sorted) {
    parts.push(Buffer.from(`${entry.mode} ${entry.name}\0`, 'utf8'));
    parts.push(Buffer.from(entry.oid, 'hex'));
  }
  return Buffer.concat(parts);
}
// Flatten a tree into path -> {mode, oid}; recursive.
function flattenTree(repo, treeSha, prefix, out) {
  const result = out || new Map();
  if (!treeSha) return result;
  const obj = getObject(repo, treeSha);
  if (!obj || obj[0] !== 'tree') return result;
  for (const entry of parseTree(obj[1])) {
    const path = prefix ? `${prefix}/${entry.name}` : entry.name;
    if (entry.mode === '40000') flattenTree(repo, entry.oid, path, result);
    else result.set(path, { mode: entry.mode, oid: entry.oid });
  }
  return result;
}
// Rebuild nested trees from a flat path -> blob oid map; returns root tree sha.
function buildTreeFromFlat(repo, flat) {
  function buildLevel(prefix) {
    const entries = [];
    const dirs = new Map();
    for (const [path, value] of flat) {
      if (!path.startsWith(prefix)) continue;
      const rest = path.slice(prefix.length);
      const slash = rest.indexOf('/');
      if (slash === -1) entries.push({ mode: value.mode || '100644', name: rest, oid: value.oid });
      else {
        const dir = rest.slice(0, slash);
        if (!dirs.has(dir)) dirs.set(dir, []);
        dirs.get(dir).push(path);
      }
    }
    for (const dir of dirs.keys()) {
      const sub = buildLevel(`${prefix}${dir}/`);
      entries.push({ mode: '40000', name: dir, oid: sub });
    }
    return storeObject(repo, 'tree', buildTree(entries));
  }
  return buildLevel('');
}
// All objects reachable from the given tips (commits walk parents, tags peel).
function collectReachable(repo, tips) {
  const seen = new Set();
  const stack = [...tips];
  while (stack.length) {
    const sha = stack.pop();
    if (!sha || seen.has(sha)) continue;
    const obj = getObject(repo, sha);
    if (!obj) continue;
    seen.add(sha);
    const [type, data] = obj;
    if (type === 'commit') {
      const commit = parseCommit(data);
      if (commit.tree) stack.push(commit.tree);
      for (const parent of commit.parents) stack.push(parent);
    } else if (type === 'tree') {
      for (const entry of parseTree(data)) stack.push(entry.oid);
    } else if (type === 'tag') {
      const tag = parseTag(data);
      if (tag.object) stack.push(tag.object);
    }
  }
  return seen;
}
// Commit-only ancestry: is `ancestor` reachable from `descendant` via parents?
function isAncestor(repo, ancestor, descendant) {
  const seen = new Set();
  const stack = [descendant];
  while (stack.length) {
    const sha = stack.pop();
    if (sha === ancestor) return true;
    if (!sha || seen.has(sha)) continue;
    seen.add(sha);
    const obj = getObject(repo, sha);
    if (!obj) continue;
    if (obj[0] === 'commit') stack.push(...parseCommit(obj[1]).parents);
    else if (obj[0] === 'tag') {
      const tag = parseTag(obj[1]);
      if (tag.object) stack.push(tag.object);
    }
  }
  return false;
}
// Peel a ref target to its commit sha (through tag objects).
function peelToCommit(repo, sha) {
  let current = sha;
  for (let guard = 0; guard < 32; guard += 1) {
    const obj = getObject(repo, current);
    if (!obj) return null;
    if (obj[0] === 'commit') return current;
    if (obj[0] === 'tag') {
      current = parseTag(obj[1]).object;
      continue;
    }
    return null;
  }
  return null;
}
// Merge base: nearest common ancestor of two commits (BFS from both).
function mergeBase(repo, a, b) {
  if (!a || !b) return null;
  const ancestorsOf = (tip) => {
    const dist = new Map();
    const queue = [tip];
    dist.set(tip, 0);
    while (queue.length) {
      const sha = queue.shift();
      const obj = getObject(repo, sha);
      if (!obj || obj[0] !== 'commit') continue;
      for (const parent of parseCommit(obj[1]).parents) {
        if (!dist.has(parent)) {
          dist.set(parent, dist.get(sha) + 1);
          queue.push(parent);
        }
      }
    }
    return dist;
  };
  const fromA = ancestorsOf(a);
  const fromB = ancestorsOf(b);
  let best = null;
  let bestScore = Infinity;
  for (const [sha, d] of fromA) {
    if (fromB.has(sha)) {
      const score = d + fromB.get(sha);
      if (score < bestScore) {
        bestScore = score;
        best = sha;
      }
    }
  }
  return best;
}
// Commit history from a tip, newest first (BFS over parents).
function historyFrom(repo, tip) {
  const order = [];
  const seen = new Set();
  const queue = [tip];
  while (queue.length) {
    const sha = queue.shift();
    if (!sha || seen.has(sha)) continue;
    const obj = getObject(repo, sha);
    if (!obj || obj[0] !== 'commit') continue;
    seen.add(sha);
    order.push(sha);
    queue.push(...parseCommit(obj[1]).parents);
  }
  return order;
}

// ---------------------------------------------------------------------------
// Packfiles
function adler32(data) {
  const MOD = 65521;
  let a = 1;
  let b = 0;
  let i = 0;
  while (i < data.length) {
    const end = Math.min(i + 5552, data.length);
    for (; i < end; i += 1) {
      a += data[i];
      b += a;
    }
    a %= MOD;
    b %= MOD;
  }
  return ((b << 16) | a) >>> 0;
}
function inflateExact(buffer, offset) {
  // zlib streams are self-terminating and inflateSync tolerates trailing
  // bytes. One full inflate yields the data; the stream ends with the
  // Adler-32 of that data, so the trailer's position marks the exact end
  // and one verify inflate confirms it. (The old code binary-searched the
  // end with a full inflate per step, ~log2(n) inflates per pack entry.)
  const rest = buffer.subarray(offset);
  let data;
  try {
    data = zlib.inflateSync(rest);
  } catch {
    throw new Error('corrupt zlib stream in pack');
  }
  const trailer = Buffer.alloc(4);
  trailer.writeUInt32BE(adler32(data), 0);
  let at = rest.indexOf(trailer, 4);
  while (at >= 0) {
    const end = at + 4;
    try {
      if (zlib.inflateSync(rest.subarray(0, end)).equals(data)) return { data, consumed: end };
    } catch {
      // not the real trailer; keep looking
    }
    at = rest.indexOf(trailer, at + 1);
  }
  // Fallback: the smallest prefix that inflates.
  let lo = 1;
  let hi = rest.length;
  let best = -1;
  while (lo <= hi) {
    const mid = (lo + hi) >> 1;
    try {
      zlib.inflateSync(rest.subarray(0, mid));
      best = mid;
      hi = mid - 1;
    } catch {
      lo = mid + 1;
    }
  }
  if (best < 0) throw new Error('corrupt zlib stream in pack');
  return { data, consumed: best };
}
function applyDelta(base, delta) {
  let pos = 0;
  const readVarint = () => {
    let value = 0;
    let shift = 0;
    for (;;) {
      const byte = delta[pos];
      pos += 1;
      value |= (byte & 0x7f) << shift;
      shift += 7;
      if (!(byte & 0x80)) break;
    }
    return value;
  };
  const sourceSize = readVarint();
  if (sourceSize !== base.length) throw new Error('delta base size mismatch');
  const targetSize = readVarint();
  const out = [];
  while (pos < delta.length) {
    const opcode = delta[pos];
    pos += 1;
    if (opcode & 0x80) {
      let offset = 0;
      let size = 0;
      for (let i = 0; i < 4; i += 1) if (opcode & (1 << i)) { offset |= delta[pos] << (8 * i); pos += 1; }
      for (let i = 0; i < 3; i += 1) if (opcode & (0x10 << i)) { size |= delta[pos] << (8 * i); pos += 1; }
      if (size === 0) size = 0x10000;
      out.push(base.subarray(offset, offset + size));
    } else if (opcode > 0) {
      out.push(delta.subarray(pos, pos + opcode));
      pos += opcode;
    } else {
      throw new Error('bad delta opcode');
    }
  }
  const result = Buffer.concat(out);
  if (result.length !== targetSize) throw new Error('delta target size mismatch');
  return result;
}
// Parse a pack into the repo's store; returns the list of object shas stored.
function unpackPack(repo, pack) {
  if (pack.length < 12 + 20) throw new Error('pack too small');
  if (pack.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('bad pack signature');
  const version = pack.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new Error(`pack version ${version}`);
  const count = pack.readUInt32BE(8);
  let pos = 12;
  const pending = []; // [typeName|null, data, baseRef]
  const stored = [];
  const localByOffset = new Map(); // pack offset -> [type, data]
  for (let index = 0; index < count; index += 1) {
    const entryOffset = pos;
    let byte = pack[pos];
    pos += 1;
    const typeCode = (byte >> 4) & 7;
    let size = byte & 0x0f;
    let shift = 4;
    while (byte & 0x80) {
      byte = pack[pos];
      pos += 1;
      size |= (byte & 0x7f) << shift;
      shift += 7;
    }
    let base = null;
    if (typeCode === 6) {
      // ofs-delta: negative offset varint
      let offsetByte = pack[pos];
      pos += 1;
      let offset = offsetByte & 0x7f;
      while (offsetByte & 0x80) {
        offsetByte = pack[pos];
        pos += 1;
        offset = ((offset + 1) << 7) | (offsetByte & 0x7f);
      }
      base = { kind: 'offset', offset: entryOffset - offset };
    } else if (typeCode === 7) {
      base = { kind: 'oid', oid: pack.subarray(pos, pos + 20).toString('hex') };
      pos += 20;
    }
    const { data, consumed } = inflateExact(pack, pos);
    pos += consumed;
    if (data.length !== size) throw new Error('pack entry size mismatch');
    if (typeCode >= 1 && typeCode <= 4) {
      const type = TYPE_NAMES[typeCode];
      const sha = storeObject(repo, type, data);
      localByOffset.set(entryOffset, [type, data]);
      stored.push(sha);
    } else if (base) {
      pending.push({ data, base, entryOffset });
    } else {
      throw new Error(`bad pack type ${typeCode}`);
    }
  }
  // Resolve deltas (a delta's base may itself be a delta resolved below).
  const resolveEntry = (entry) => {
    let baseType;
    let baseData;
    if (entry.base.kind === 'offset') {
      const found = localByOffset.get(entry.base.offset);
      if (!found) throw new Error('delta base offset not in pack');
      [baseType, baseData] = found;
    } else {
      const found = getObject(repo, entry.base.oid);
      if (!found) throw new Error('delta base not found');
      [baseType, baseData] = found;
    }
    const data = applyDelta(baseData, entry.data);
    const sha = storeObject(repo, baseType, data);
    localByOffset.set(entry.entryOffset, [baseType, data]);
    return sha;
  };
  let guard = pending.length + 2;
  while (pending.length && guard > 0) {
    guard -= 1;
    const still = [];
    for (const entry of pending) {
      try {
        stored.push(resolveEntry(entry));
      } catch {
        still.push(entry);
      }
    }
    if (still.length === pending.length) throw new Error('unresolvable delta chain');
    pending.length = 0;
    pending.push(...still);
  }
  if (pending.length) throw new Error('unresolvable delta chain');
  return stored;
}
function writePack(repo, shas) {
  const parts = [];
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(shas.length, 8);
  parts.push(header);
  for (const sha of shas) {
    const [type, data] = getObject(repo, sha);
    const code = TYPE_CODES[type];
    let size = data.length;
    const first = (code << 4) | (size & 0x0f);
    size >>= 4;
    const bytes = [size > 0 ? first | 0x80 : first];
    while (size > 0) {
      const next = size & 0x7f;
      size >>= 7;
      bytes.push(size > 0 ? next | 0x80 : next);
    }
    parts.push(Buffer.from(bytes));
    // Level 1: the wire only needs a valid zlib stream, and CPU is the
    // scarce resource in the pod; the size difference is a few percent.
    parts.push(zlib.deflateSync(data, { level: 1 }));
  }
  const body = Buffer.concat(parts);
  const trailer = crypto.createHash('sha1').update(body).digest();
  return Buffer.concat([body, trailer]);
}

// ---------------------------------------------------------------------------
// pkt-line framing
function pktLine(payload) {
  const data = Buffer.isBuffer(payload) ? payload : Buffer.from(payload, 'utf8');
  const length = data.length + 4;
  const head = Buffer.from(length.toString(16).padStart(4, '0'), 'ascii');
  return Buffer.concat([head, data]);
}
const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');
function pktText(text) {
  return pktLine(Buffer.from(text, 'utf8'));
}
// Decode a buffer as pkt-lines; returns packets and the offset just past
// the first flush packet (where a packfile would start).
function decodePktLines(buffer, startAt, stopAtFlush) {
  const packets = [];
  let pos = startAt || 0;
  let flushEnd = -1;
  while (pos + 4 <= buffer.length) {
    const header = buffer.subarray(pos, pos + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(header)) throw new Error('invalid pkt-line header');
    const length = parseInt(header, 16);
    if (length === 0) {
      packets.push({ kind: 'flush' });
      pos += 4;
      if (flushEnd === -1) flushEnd = pos;
      if (stopAtFlush) break;
      continue;
    }
    if (length === 1) {
      packets.push({ kind: 'delim' });
      pos += 4;
      continue;
    }
    if (length === 2) {
      packets.push({ kind: 'response-end' });
      pos += 4;
      continue;
    }
    if (length < 4 || pos + length > buffer.length) throw new Error('truncated pkt-line');
    packets.push({ kind: 'data', payload: buffer.subarray(pos + 4, pos + length) });
    pos += length;
  }
  return { packets, next: flushEnd === -1 ? pos : flushEnd };
}
function sidebandChunks(data, band) {
  const chunks = [];
  const MAX = 65504;
  if (data.length === 0) {
    chunks.push(pktLine(Buffer.from([band])));
    return chunks;
  }
  for (let offset = 0; offset < data.length; offset += MAX) {
    const slice = data.subarray(offset, Math.min(data.length, offset + MAX));
    chunks.push(pktLine(Buffer.concat([Buffer.from([band]), slice])));
  }
  return chunks;
}

// ---------------------------------------------------------------------------
// HTTP plumbing
function sendJsonBody(res, status, body, extraHeaders) {
  const headers = {
    'content-type': 'application/json; charset=utf-8',
    'x-github-request-id': `req-${(requestSeq += 1)}`,
  };
  if (extraHeaders) {
    for (const name of Object.keys(extraHeaders)) headers[name] = extraHeaders[name];
  }
  res.writeHead(status, headers);
  res.end(body);
}
function sendJson(res, status, value, extraHeaders) {
  sendJsonBody(res, status, Buffer.from(JSON.stringify(value), 'utf8'), extraHeaders);
}
function sendError(res, status, message) {
  sendJson(res, status, { message });
}
function readBody(req) {
  return new Promise((resolve, reject) => {
    const chunks = [];
    req.on('data', (chunk) => chunks.push(chunk));
    // Most bodies arrive as one chunk; concatenating a single chunk
    // would only copy it, so hand it back as it is.
    req.on('end', () => resolve(chunks.length === 1 ? chunks[0] : Buffer.concat(chunks)));
    req.on('error', reject);
  });
}
function authed(req) {
  const header = req.headers.authorization || '';
  if (!header.startsWith('Bearer ')) return false;
  const presented = header.slice(7);
  if (TOKEN) return presented === TOKEN;
  return presented.length > 0;
}

// ---------------------------------------------------------------------------
// Git smart HTTP
function sortedRefs(repo) {
  return [...repo.refs.entries()].sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0));
}
function headTarget(repo) {
  return `refs/heads/${repo.defaultBranch}`;
}
function advertiseV0(repo, service) {
  const parts = [pktText(`# service=${service}\n`), PKT_FLUSH];
  const caps =
    service === 'git-upload-pack'
      ? `multi_ack_detailed side-band-64k thin-pack ofs-delta agent=forge/1.0 symref=HEAD:${headTarget(repo)} object-format=sha1`
      : `report-status side-band-64k delete-refs ofs-delta quiet agent=forge/1.0 symref=HEAD:${headTarget(repo)} object-format=sha1`;
  const lines = [];
  const headSha = repo.refs.get(headTarget(repo));
  if (repo.refs.size === 0) {
    lines.push(`${ZERO} capabilities^{}\0${caps}\n`);
  } else {
    lines.push(`${headSha || ZERO} HEAD\0${caps}\n`);
    for (const [ref, sha] of sortedRefs(repo)) {
      lines.push(`${sha} ${ref}\n`);
      const obj = getObject(repo, sha);
      if (obj && obj[0] === 'tag') {
        const peeled = peelToCommit(repo, sha);
        if (peeled && peeled !== sha) lines.push(`${peeled} ${ref}^{}\n`);
      }
    }
  }
  for (let i = 0; i < lines.length; i += 1) parts.push(pktText(lines[i]));
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}
function advertiseV2() {
  const lines = [
    'version 2\n',
    'agent=forge/1.0\n',
    'ls-refs=unborn\n',
    'fetch=shallow filter\n',
    'server-option\n',
    'object-format=sha1\n',
  ];
  return Buffer.concat([pktText('# service=git-upload-pack\n'), PKT_FLUSH, ...lines.map(pktText), PKT_FLUSH]);
}
// The v2 capability advertisement is the same bytes for every repository
// and every request, so build it once and share the buffer.
const ADVERTISE_V2_BODY = advertiseV2();
function lsRefs(repo, args) {
  const peel = args.has('peel');
  const symrefs = args.has('symrefs');
  const unborn = args.has('unborn');
  const prefixes = [];
  for (const arg of args) if (arg.startsWith('ref-prefix ')) prefixes.push(arg.slice(11));
  const matches = (name) => prefixes.length === 0 || prefixes.some((prefix) => name.startsWith(prefix));
  const lines = [];
  const target = headTarget(repo);
  const headSha = repo.refs.get(target);
  if (matches('HEAD')) {
    if (headSha) {
      lines.push(`${headSha} HEAD${symrefs ? ` symref-target:${target}` : ''}\n`);
    } else if (unborn) {
      lines.push(`unborn HEAD${symrefs ? ` symref-target:${target}` : ''}\n`);
    }
  }
  for (const [ref, sha] of sortedRefs(repo)) {
    if (!matches(ref)) continue;
    let line = `${sha} ${ref}`;
    if (peel) {
      const obj = getObject(repo, sha);
      if (obj && obj[0] === 'tag') {
        const peeled = peelToCommit(repo, sha);
        if (peeled) line += ` peeled:${peeled}`;
      }
    }
    lines.push(`${line}\n`);
  }
  return Buffer.concat([...lines.map(pktText), PKT_FLUSH]);
}
// An ls-refs reply is a pure function of the ref map, the object store
// (tag peeling) and the argument set, so finished bytes are cached per
// repository under both version counters: a clone asks the identical
// question right after its capability request, fifty times in a row.
function lsRefsReply(repo, args) {
  const key = `${repo.storeVersion}|${repo.refsVersion}|${[...args].sort().join('\n')}`;
  const hit = repo.lsRefsCache.get(key);
  if (hit) return hit;
  const reply = lsRefs(repo, args);
  if (repo.lsRefsCache.size >= 64) repo.lsRefsCache.clear();
  repo.lsRefsCache.set(key, reply);
  return reply;
}
// Compute the object set for a fetch. Handles haves (with shallow cut) and
// depth limiting; returns {objects:Set, shallow:[], unshallow:[]}.
function computeFetch(repo, wants, haves, shallowList, depth) {
  const shallowSet = new Set(shallowList);
  // Objects the client already holds: full closure of haves, except that a
  // shallow boundary commit's parents are not held.
  const held = new Set();
  {
    const stack = [...haves];
    while (stack.length) {
      const sha = stack.pop();
      if (!sha || held.has(sha)) continue;
      const obj = getObject(repo, sha);
      if (!obj) continue;
      held.add(sha);
      const [type, data] = obj;
      if (type === 'commit') {
        const commit = parseCommit(data);
        if (commit.tree) stack.push(commit.tree);
        if (!shallowSet.has(sha)) for (const parent of commit.parents) stack.push(parent);
      } else if (type === 'tree') {
        for (const entry of parseTree(data)) stack.push(entry.oid);
      } else if (type === 'tag') {
        const tag = parseTag(data);
        if (tag.object) stack.push(tag.object);
      }
    }
  }
  // Included commits: within `depth` of a want (want counts as generation 1).
  let includedCommits = null;
  if (depth != null && depth > 0) {
    includedCommits = new Set();
    const dist = new Map();
    const queue = [];
    for (const want of wants) {
      const commit = peelToCommit(repo, want);
      if (commit && !dist.has(commit)) {
        dist.set(commit, 1);
        queue.push(commit);
      }
    }
    while (queue.length) {
      const sha = queue.shift();
      const d = dist.get(sha);
      if (d >= depth) continue;
      const obj = getObject(repo, sha);
      if (!obj || obj[0] !== 'commit') continue;
      for (const parent of parseCommit(obj[1]).parents) {
        if (!dist.has(parent)) {
          dist.set(parent, d + 1);
          queue.push(parent);
        }
      }
    }
    for (const [sha, d] of dist) if (d <= depth) includedCommits.add(sha);
  }
  let wanted;
  if (includedCommits) {
    wanted = new Set();
    const stack = [...wants];
    const seenTags = new Set();
    while (stack.length) {
      const sha = stack.pop();
      if (!sha || seenTags.has(sha)) continue;
      seenTags.add(sha);
      const obj = getObject(repo, sha);
      if (!obj) continue;
      if (obj[0] === 'tag') {
        wanted.add(sha);
        const tag = parseTag(obj[1]);
        if (tag.object) stack.push(tag.object);
        continue;
      }
      if (obj[0] !== 'commit') continue;
      // walk commits but include only those inside the depth budget
      const inner = [sha];
      const seenCommits = new Set();
      while (inner.length) {
        const commitSha = inner.pop();
        if (seenCommits.has(commitSha) || !includedCommits.has(commitSha)) continue;
        seenCommits.add(commitSha);
        wanted.add(commitSha);
        const commitObj = getObject(repo, commitSha);
        const commit = parseCommit(commitObj[1]);
        const treeStack = [commit.tree];
        const seenTrees = new Set();
        while (treeStack.length) {
          const treeSha = treeStack.pop();
          if (!treeSha || seenTrees.has(treeSha)) continue;
          seenTrees.add(treeSha);
          wanted.add(treeSha);
          const treeObj = getObject(repo, treeSha);
          if (!treeObj) continue;
          for (const entry of parseTree(treeObj[1])) {
            if (entry.mode === '40000') treeStack.push(entry.oid);
            else wanted.add(entry.oid);
          }
        }
        for (const parent of commit.parents) inner.push(parent);
      }
    }
  } else {
    wanted = collectReachable(repo, wants);
  }
  const objects = new Set();
  for (const sha of wanted) if (!held.has(sha)) objects.add(sha);
  // Boundary bookkeeping for shallow replies.
  const shallowOut = [];
  const unshallowOut = [];
  if (depth != null && depth > 0) {
    for (const sha of includedCommits) {
      if (!objects.has(sha) && !wants.includes(sha) && !includedCommits.has(sha)) continue;
      const obj = getObject(repo, sha);
      if (!obj || obj[0] !== 'commit') continue;
      const parents = parseCommit(obj[1]).parents;
      const isBoundary = parents.some((p) => !includedCommits.has(p) && !shallowSet.has(p));
      if (isBoundary && (objects.has(sha) || haves.includes(sha) || wants.includes(sha))) shallowOut.push(sha);
    }
    for (const sha of shallowSet) {
      const obj = getObject(repo, sha);
      if (!obj || obj[0] !== 'commit') continue;
      const parents = parseCommit(obj[1]).parents;
      if (parents.length && parents.every((p) => includedCommits.has(p))) unshallowOut.push(sha);
    }
  }
  return { objects, shallow: shallowOut, unshallow: unshallowOut };
}
function fetchPack(repo, wants, haves, shallowList, depth) {
  // A fetch's result is a pure function of the object store and the request,
  // so identical requests against an unchanged store reuse the built pack
  // (the clone workload asks for the same shallow pack 50 times in a row).
  const key = [
    repo.storeVersion,
    depth == null ? '' : depth,
    [...wants].sort().join(','),
    [...haves].sort().join(','),
    [...shallowList].sort().join(','),
  ].join('|');
  const cached = repo.packCache.get(key);
  if (cached) return cached;
  const { objects, shallow, unshallow } = computeFetch(repo, wants, haves, shallowList, depth);
  const pack = writePack(repo, [...objects]);
  const result = { pack, shallow, unshallow, count: objects.size };
  if (repo.packCache.size >= 32) repo.packCache.clear();
  repo.packCache.set(key, result);
  return result;
}
// The whole upload-pack reply (acknowledgments, shallow notes and the
// packfile section) is a pure function of the object store and the
// request, so cache the finished bytes per repository: only the first
// of fifty identical clone fetches pays for framing and concatenation.
function fetchReply(repo, variant, request, build) {
  const key = [
    variant,
    repo.storeVersion,
    request.depth == null ? '' : request.depth,
    [...request.wants].sort().join(','),
    [...request.haves].sort().join(','),
    [...request.shallow].sort().join(','),
  ].join('|');
  const hit = repo.fetchCache.get(key);
  if (hit) return hit;
  const reply = build();
  if (repo.fetchCache.size >= 64) repo.fetchCache.clear();
  repo.fetchCache.set(key, reply);
  return reply;
}

function gitInfoRefs(req, res, repo, service, isV2) {
  if (!repo) {
    res.writeHead(404, { 'content-type': 'text/plain' });
    res.end('not found');
    return;
  }
  const body = service === 'git-upload-pack' && isV2 ? ADVERTISE_V2_BODY : advertiseV0(repo, service);
  res.writeHead(200, { 'content-type': `application/x-${service}-advertisement` });
  res.end(body);
}
function parseFetchArgs(lines) {
  const request = { wants: [], haves: [], shallow: [], depth: null, done: false };
  for (const line of lines) {
    if (line.startsWith('want ')) request.wants.push(line.slice(5).trim().split(' ')[0]);
    else if (line.startsWith('have ')) request.haves.push(line.slice(5).trim());
    else if (line.startsWith('shallow ')) request.shallow.push(line.slice(8).trim());
    else if (line.startsWith('deepen ')) request.depth = parseInt(line.slice(7).trim(), 10);
    else if (line === 'done') request.done = true;
  }
  return request;
}
function gitUploadPack(req, res, repo, body) {
  if (!repo) {
    res.writeHead(404, { 'content-type': 'text/plain' });
    res.end('not found');
    return;
  }
  let decoded;
  try {
    decoded = decodePktLines(body, 0);
  } catch {
    res.writeHead(400, { 'content-type': 'text/plain' });
    res.end('invalid pkt-line');
    return;
  }
  const lines = decoded.packets.filter((p) => p.kind === 'data').map((p) => p.payload.toString('utf8').replace(/\n$/, ''));
  const isV2 = lines.some((line) => line.startsWith('command='));
  if (isV2) {
    const command = lines.find((line) => line.startsWith('command=')).slice(8);
    if (command === 'ls-refs') {
      const args = new Set(lines.slice(1));
      const reply = lsRefsReply(repo, args);
      res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-result' });
      res.end(reply);
      return;
    }
    if (command === 'fetch') {
      const request = parseFetchArgs(lines.slice(1));
      const reply = fetchReply(repo, 'v2', request, () => {
        const { pack, shallow, unshallow } = fetchPack(repo, request.wants, request.haves, request.shallow, request.depth);
        const parts = [];
        if (request.haves.length) {
          parts.push(pktText('acknowledgments\n'));
          const common = request.haves.filter((sha) => getObject(repo, sha));
          if (common.length) {
            for (const sha of common) parts.push(pktText(`ACK ${sha}\n`));
            parts.push(pktText('ready\n'));
          } else {
            parts.push(pktText('NAK\n'));
          }
          parts.push(PKT_FLUSH);
        }
        if (shallow.length || unshallow.length) {
          parts.push(pktText('shallow-info\n'));
          for (const sha of shallow) parts.push(pktText(`shallow ${sha}\n`));
          for (const sha of unshallow) parts.push(pktText(`unshallow ${sha}\n`));
          parts.push(PKT_FLUSH);
        }
        parts.push(pktText('packfile\n'));
        for (const chunk of sidebandChunks(pack, 1)) parts.push(chunk);
        parts.push(PKT_FLUSH);
        return Buffer.concat(parts);
      });
      res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-result' });
      res.end(reply);
      return;
    }
    res.writeHead(400, { 'content-type': 'text/plain' });
    res.end('unknown command');
    return;
  }
  // Protocol v0: wants section, flush, haves/done section.
  const request = parseFetchArgs(lines);
  const reply = fetchReply(repo, 'v0', request, () => {
    const { pack, shallow, unshallow } = fetchPack(repo, request.wants, request.haves, request.shallow, request.depth);
    const parts = [];
    for (const sha of shallow) parts.push(pktText(`shallow ${sha}\n`));
    for (const sha of unshallow) parts.push(pktText(`unshallow ${sha}\n`));
    parts.push(pktText('NAK\n'));
    for (const chunk of sidebandChunks(pack, 1)) parts.push(chunk);
    parts.push(PKT_FLUSH);
    return Buffer.concat(parts);
  });
  res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-result' });
  res.end(reply);
}
function gitReceivePack(req, res, repo, body) {
  if (!repo) {
    res.writeHead(404, { 'content-type': 'text/plain' });
    res.end('not found');
    return;
  }
  let decoded;
  try {
    decoded = decodePktLines(body, 0, true);
  } catch {
    res.writeHead(400, { 'content-type': 'text/plain' });
    res.end('invalid pkt-line');
    return;
  }
  const commands = [];
  for (const packet of decoded.packets) {
    if (packet.kind !== 'data') continue;
    let text = packet.payload.toString('utf8').replace(/\n$/, '');
    const nul = text.indexOf('\0');
    if (nul >= 0) text = text.slice(0, nul);
    const match = /^([0-9a-f]{40}) ([0-9a-f]{40}) (.+)$/.exec(text);
    if (match) commands.push({ oldOid: match[1], newOid: match[2], ref: match[3] });
  }
  const rest = body.subarray(decoded.next);
  let unpackLine = 'unpack ok\n';
  const needsPack = commands.some((command) => command.newOid !== ZERO);
  if (needsPack) {
    try {
      unpackPack(repo, rest);
    } catch (error) {
      unpackLine = `unpack ${error.message}\n`;
    }
  }
  const reports = [];
  if (unpackLine === 'unpack ok\n') {
    for (const command of commands) {
      const current = repo.refs.get(command.ref) || ZERO;
      let failure = null;
      if (command.newOid === ZERO) {
        if (!repo.refs.has(command.ref)) failure = 'reference does not exist';
        else if (command.oldOid !== ZERO && command.oldOid !== current) failure = 'stale info';
      } else if (command.oldOid === ZERO) {
        if (repo.refs.has(command.ref)) failure = 'reference already exists';
        else if (!getObject(repo, command.newOid)) failure = 'missing object';
      } else {
        if (command.oldOid !== current) failure = 'stale info';
        else if (command.newOid !== current && !isAncestor(repo, current, command.newOid)) failure = 'non-fast-forward';
      }
      if (failure) {
        reports.push(`ng ${command.ref} ${failure}\n`);
      } else {
        if (command.newOid === ZERO) repo.refs.delete(command.ref);
        else repo.refs.set(command.ref, command.newOid);
        repo.refsVersion += 1;
        reports.push(`ok ${command.ref}\n`);
      }
    }
  } else {
    for (const command of commands) reports.push(`ng ${command.ref} unpack-error\n`);
  }
  const reportText = Buffer.concat([pktText(unpackLine), ...reports.map((line) => pktText(line)), PKT_FLUSH]);
  const parts = [...sidebandChunks(reportText, 1), PKT_FLUSH];
  res.writeHead(200, { 'content-type': 'application/x-git-receive-pack-result' });
  res.end(Buffer.concat(parts));
}

// ---------------------------------------------------------------------------
// Shared domain operations (REST, GraphQL and MCP all act on these)
function userJson() {
  return { login: VIEWER.login, id: VIEWER.id, type: 'User', name: VIEWER.name, email: VIEWER.email };
}
// The viewer object is identical in every response and is only ever
// serialized, never mutated, so one shared instance serves all of them.
const USER_JSON = userJson();
function repoJson(repo, base) {
  return {
    id: repo.id,
    node_id: globalId('Repository', repo.id),
    name: repo.name,
    full_name: `${repo.owner}/${repo.name}`,
    private: repo.private,
    owner: USER_JSON,
    description: repo.description,
    html_url: `${base}/${repo.owner}/${repo.name}`,
    url: `${base}/api/v3/repos/${repo.owner}/${repo.name}`,
    clone_url: `${base}/${repo.owner}/${repo.name}.git`,
    created_at: NOW_ISO,
    updated_at: NOW_ISO,
    pushed_at: NOW_ISO,
    size: 0,
    default_branch: repo.defaultBranch,
    has_issues: true,
    visibility: repo.private ? 'private' : 'public',
  };
}
function globalId(type, key) {
  return Buffer.from(`${type}:${key}`, 'utf8').toString('base64');
}
function parseGlobalId(id) {
  try {
    const text = Buffer.from(String(id), 'base64').toString('utf8');
    const colon = text.indexOf(':');
    if (colon < 0) return null;
    return { type: text.slice(0, colon), key: text.slice(colon + 1) };
  } catch {
    return null;
  }
}
function branchTip(repo, branch) {
  return repo.refs.get(`refs/heads/${branch}`) || null;
}
function commitTreeFlat(repo, commitSha) {
  if (!commitSha) return new Map();
  const obj = getObject(repo, commitSha);
  if (!obj || obj[0] !== 'commit') return new Map();
  return flattenTree(repo, parseCommit(obj[1]).tree);
}
// Write a file change (or deletion when blobSha is null) as a new commit on a
// branch; creates the branch from the default branch (or unborn) if needed.
function commitFileChange(repo, branch, path, blobSha, message) {
  let tip = branchTip(repo, branch);
  if (!tip) {
    tip = branchTip(repo, repo.defaultBranch);
    if (tip) {
      repo.refs.set(`refs/heads/${branch}`, tip);
      repo.refsVersion += 1;
    }
  }
  const flat = commitTreeFlat(repo, tip);
  if (blobSha === null) flat.delete(path);
  else flat.set(path, { mode: '100644', oid: blobSha });
  const tree = buildTreeFromFlat(repo, flat);
  const parents = tip ? [tip] : [];
  const commit = storeObject(repo, 'commit', buildCommit(tree, parents, message || ''));
  repo.refs.set(`refs/heads/${branch}`, commit);
  repo.refsVersion += 1;
  return commit;
}
function labelJson(label) {
  return { id: label.id, name: label.name, color: label.color, description: label.description || null, default: false };
}
function issueJson(repo, entry, base) {
  return {
    id: entry.id,
    node_id: globalId('Issue', entry.id),
    number: entry.number,
    title: entry.title,
    body: entry.body,
    state: entry.state,
    labels: entry.labels.map((name) => {
      const label = repo.labels.get(name);
      return label ? labelJson(label) : { name, color: 'ededed' };
    }),
    user: USER_JSON,
    comments: entry.comments.length,
    created_at: NOW_ISO,
    updated_at: NOW_ISO,
    closed_at: entry.state === 'closed' ? NOW_ISO : null,
    html_url: `${base}/${repo.owner}/${repo.name}/issues/${entry.number}`,
    url: `${base}/api/v3/repos/${repo.owner}/${repo.name}/issues/${entry.number}`,
  };
}
function commentJson(comment) {
  return {
    id: comment.id,
    node_id: globalId('IssueComment', comment.id),
    body: comment.body,
    user: USER_JSON,
    created_at: NOW_ISO,
    updated_at: NOW_ISO,
  };
}
function pullJson(repo, entry, base) {
  const headSha = branchTip(repo, entry.pull.headRef) || entry.pull.headSha || ZERO;
  const baseSha = branchTip(repo, entry.pull.baseRef) || entry.pull.baseSha || ZERO;
  return {
    id: entry.id,
    node_id: globalId('PullRequest', entry.id),
    number: entry.number,
    title: entry.title,
    body: entry.body,
    state: entry.state,
    merged: entry.pull.merged,
    merged_at: entry.pull.merged ? NOW_ISO : null,
    merge_commit_sha: entry.pull.mergeCommitSha || null,
    user: USER_JSON,
    head: {
      label: `${repo.owner}:${entry.pull.headRef}`,
      ref: entry.pull.headRef,
      sha: headSha,
      repo: repoJson(repo, base),
    },
    base: {
      label: `${repo.owner}:${entry.pull.baseRef}`,
      ref: entry.pull.baseRef,
      sha: baseSha,
      repo: repoJson(repo, base),
    },
    created_at: NOW_ISO,
    updated_at: NOW_ISO,
    html_url: `${base}/${repo.owner}/${repo.name}/pull/${entry.number}`,
    url: `${base}/api/v3/repos/${repo.owner}/${repo.name}/pulls/${entry.number}`,
  };
}
function createEntry(repo, fields) {
  const entry = {
    id: nextEntryId++,
    number: repo.nextNumber++,
    seq: (repo.seq += 1),
    rev: 0, // bumps on every mutation of this entry (see the rev += 1 sites)
    title: fields.title || '',
    body: fields.body || '',
    state: 'open',
    labels: fields.labels || [],
    comments: [],
    pull: fields.pull || null,
  };
  repo.entries.set(entry.number, entry);
  return entry;
}
// Changed files between a pull request's merge base and its head tip.
function pullFiles(repo, entry) {
  const headTip = branchTip(repo, entry.pull.headRef);
  const baseTip = branchTip(repo, entry.pull.baseRef);
  if (!headTip || !baseTip) return [];
  const base = mergeBase(repo, peelToCommit(repo, baseTip), peelToCommit(repo, headTip));
  const ancestorFlat = commitTreeFlat(repo, base);
  const headFlat = commitTreeFlat(repo, peelToCommit(repo, headTip));
  const files = [];
  const paths = new Set([...ancestorFlat.keys(), ...headFlat.keys()]);
  for (const path of [...paths].sort()) {
    const before = ancestorFlat.get(path);
    const after = headFlat.get(path);
    if (before && after && before.oid === after.oid) continue;
    let status = 'modified';
    if (!before) status = 'added';
    if (!after) status = 'removed';
    const beforeText = before ? getObject(repo, before.oid)[1].toString('utf8') : '';
    const afterText = after ? getObject(repo, after.oid)[1].toString('utf8') : '';
    const { additions, deletions } = lineDiff(beforeText, afterText);
    files.push({
      sha: after ? after.oid : before.oid,
      filename: path,
      status,
      additions,
      deletions,
      changes: additions + deletions,
    });
  }
  return files;
}
function lineDiff(beforeText, afterText) {
  if (beforeText === afterText) return { additions: 0, deletions: 0 };
  const a = beforeText === '' ? [] : beforeText.split('\n');
  const b = afterText === '' ? [] : afterText.split('\n');
  // LCS over lines; the texts the suite diffs are small.
  const m = a.length;
  const n = b.length;
  const dp = Array.from({ length: m + 1 }, () => new Uint32Array(n + 1));
  for (let i = m - 1; i >= 0; i -= 1) {
    for (let j = n - 1; j >= 0; j -= 1) {
      dp[i][j] = a[i] === b[j] ? dp[i + 1][j + 1] + 1 : Math.max(dp[i + 1][j], dp[i][j + 1]);
    }
  }
  const common = dp[0][0];
  return { additions: n - common, deletions: m - common };
}
// Three-way tree merge; returns {tree} or {conflict:true}.
function mergeTrees(repo, entry) {
  const headTip = peelToCommit(repo, branchTip(repo, entry.pull.headRef));
  const baseTip = peelToCommit(repo, branchTip(repo, entry.pull.baseRef));
  if (!headTip || !baseTip) return { conflict: true };
  const base = mergeBase(repo, baseTip, headTip);
  const ancestorFlat = commitTreeFlat(repo, base);
  const baseFlat = commitTreeFlat(repo, baseTip);
  const headFlat = commitTreeFlat(repo, headTip);
  const result = new Map(baseFlat);
  const paths = new Set([...ancestorFlat.keys(), ...baseFlat.keys(), ...headFlat.keys()]);
  for (const path of paths) {
    const anc = ancestorFlat.get(path);
    const bas = baseFlat.get(path);
    const hed = headFlat.get(path);
    const ancOid = anc ? anc.oid : null;
    const basOid = bas ? bas.oid : null;
    const hedOid = hed ? hed.oid : null;
    if (hedOid === basOid) continue;
    if (ancOid === basOid) {
      if (hed) result.set(path, hed);
      else result.delete(path);
      continue;
    }
    if (ancOid === hedOid) continue;
    return { conflict: true };
  }
  return { tree: buildTreeFromFlat(repo, result), baseTip };
}
function mergeEntry(repo, entry) {
  if (entry.pull.merged) return { error: 'already-merged' };
  const merged = mergeTrees(repo, entry);
  if (merged.conflict) return { error: 'conflict' };
  const commit = storeObject(repo, 'commit', buildCommit(merged.tree, [merged.baseTip], entry.title));
  repo.refs.set(`refs/heads/${entry.pull.baseRef}`, commit);
  repo.refsVersion += 1;
  entry.pull.merged = true;
  entry.pull.mergeCommitSha = commit;
  entry.state = 'closed';
  entry.rev += 1;
  return { sha: commit };
}
function pullMergeable(repo, entry) {
  if (entry.pull.merged || entry.state !== 'open') return 'UNKNOWN';
  return mergeTrees(repo, entry).conflict ? 'CONFLICTING' : 'MERGEABLE';
}

// ---------------------------------------------------------------------------
// REST v3
let nextLabelId = 1;
function parseIdent(line) {
  const match = /^(.*) <(.*)> (\d+) ([+-]\d{4})$/.exec(line || '');
  if (!match) return { name: VIEWER.name, email: VIEWER.email, date: NOW_ISO };
  return { name: match[1], email: match[2], date: new Date(Number(match[3]) * 1000).toISOString().replace(/\.\d+Z$/, 'Z') };
}
function commitJson(repo, sha) {
  const obj = getObject(repo, sha);
  const commit = parseCommit(obj[1]);
  return {
    sha,
    node_id: globalId('Commit', sha),
    commit: {
      message: commit.message.replace(/\n$/, ''),
      tree: { sha: commit.tree },
      author: parseIdent(commit.author),
      committer: parseIdent(commit.committer),
    },
    author: userJson(),
    committer: userJson(),
    parents: commit.parents.map((parent) => ({ sha: parent })),
  };
}
function applyPagination(req, res, items) {
  const url = new URL(req.url, `http://${req.headers.host || 'localhost'}`);
  const perPageRaw = parseInt(url.searchParams.get('per_page') || '30', 10);
  const pageRaw = parseInt(url.searchParams.get('page') || '1', 10);
  const perPage = Number.isFinite(perPageRaw) && perPageRaw > 0 ? Math.min(perPageRaw, 100) : 30;
  const page = Number.isFinite(pageRaw) && pageRaw > 0 ? pageRaw : 1;
  const totalPages = Math.max(1, Math.ceil(items.length / perPage));
  if (page < totalPages) {
    const next = new URL(url.toString());
    next.searchParams.set('page', String(page + 1));
    next.searchParams.set('per_page', String(perPage));
    const last = new URL(url.toString());
    last.searchParams.set('page', String(totalPages));
    last.searchParams.set('per_page', String(perPage));
    res.setHeader('link', `<${next.toString()}>; rel="next", <${last.toString()}>; rel="last"`);
  }
  return items.slice((page - 1) * perPage, page * perPage);
}
function treeEntryAt(repo, rootTreeSha, segments) {
  // Walk tree objects; returns {kind:'file'|'dir', sha, size} or null.
  let current = rootTreeSha;
  for (let i = 0; i < segments.length; i += 1) {
    const obj = getObject(repo, current);
    if (!obj || obj[0] !== 'tree') return null;
    const entry = parseTree(obj[1]).find((candidate) => candidate.name === segments[i]);
    if (!entry) return null;
    if (i === segments.length - 1) {
      if (entry.mode === '40000') return { kind: 'dir', sha: entry.oid, size: 0 };
      const blob = getObject(repo, entry.oid);
      return { kind: 'file', sha: entry.oid, size: blob ? blob[1].length : 0, mode: entry.mode };
    }
    if (entry.mode !== '40000') return null;
    current = entry.oid;
  }
  return { kind: 'dir', sha: rootTreeSha, size: 0 };
}
function dirListing(repo, dirTreeSha, prefixPath) {
  const obj = getObject(repo, dirTreeSha);
  if (!obj) return [];
  return parseTree(obj[1])
    .map((entry) => {
      const isDir = entry.mode === '40000';
      const blob = isDir ? null : getObject(repo, entry.oid);
      return {
        name: entry.name,
        path: prefixPath ? `${prefixPath}/${entry.name}` : entry.name,
        sha: entry.oid,
        size: blob ? blob[1].length : 0,
        type: isDir ? 'dir' : 'file',
      };
    })
    .sort((a, b) => (a.name < b.name ? -1 : 1));
}

function handleRest(req, res, segments, query, body, base) {
  const method = req.method;
  const jsonBody = () => {
    if (!body || body.length === 0) return {};
    try {
      return JSON.parse(body.toString('utf8'));
    } catch {
      return undefined;
    }
  };
  const needBody = () => {
    const parsed = jsonBody();
    if (parsed === undefined) {
      sendError(res, 400, 'Problems parsing JSON');
      return undefined;
    }
    return parsed;
  };
  // Root and meta
  if (segments.length === 0) {
    if (method !== 'GET') return sendError(res, 404, 'Not Found');
    return sendJson(
      res,
      200,
      { current_user_url: `${base}/api/v3/user`, current_user_repositories_url: `${base}/api/v3/user/repos` },
      { 'x-oauth-scopes': 'repo, user' },
    );
  }
  if (segments[0] === 'meta' && segments.length === 1) {
    if (method !== 'GET') return sendError(res, 404, 'Not Found');
    return sendJson(res, 200, { installed_version: '1.0.0-forge', api_version: 'v3' });
  }
  if (segments[0] === 'user' && segments.length === 1) {
    if (method !== 'GET') return sendError(res, 404, 'Not Found');
    return sendJson(res, 200, { ...userJson(), created_at: NOW_ISO, updated_at: NOW_ISO });
  }
  if (segments[0] === 'user' && segments[1] === 'repos' && segments.length === 2) {
    if (method === 'GET') {
      const mine = [...repos.values()].filter((repo) => repo.owner === VIEWER.login).sort((a, b) => a.id - b.id);
      return sendJson(res, 200, applyPagination(req, res, mine).map((repo) => repoJson(repo, base)));
    }
    if (method === 'POST') {
      const data = needBody();
      if (data === undefined) return;
      const name = data.name;
      if (typeof name !== 'string' || name === '') return sendError(res, 422, 'Validation Failed: name is required');
      if (getRepo(VIEWER.login, name)) return sendError(res, 422, 'Validation Failed: name already exists on this account');
      const repo = newRepo(VIEWER.login, name, data.description || '', data.private, data.default_branch);
      repos.set(`${VIEWER.login}/${name}`, repo);
      if (data.auto_init) {
        const blob = storeObject(repo, 'blob', Buffer.from(`# ${name}\n`, 'utf8'));
        commitFileChange(repo, repo.defaultBranch, 'README.md', blob, 'Initial commit');
      }
      return sendJson(res, 201, repoJson(repo, base));
    }
    return sendError(res, 404, 'Not Found');
  }
  if (segments[0] !== 'repos' || segments.length < 3) return sendError(res, 404, 'Not Found');
  const owner = segments[1];
  const name = segments[2];
  const repo = owner === VIEWER.login ? getRepo(owner, name) : null;
  if (!repo) return sendError(res, 404, 'Not Found');
  const rest = segments.slice(3);
  const repoBase = `${base}/api/v3/repos/${owner}/${name}`;

  if (rest.length === 0) {
    if (method === 'GET') return sendJson(res, 200, repoJson(repo, base));
    if (method === 'PATCH') {
      const data = needBody();
      if (data === undefined) return;
      if (typeof data.description === 'string') repo.description = data.description;
      if (typeof data.private === 'boolean') repo.private = data.private;
      if (typeof data.name === 'string' && data.name !== repo.name && !getRepo(owner, data.name)) {
        repos.delete(`${owner}/${repo.name}`);
        repo.name = data.name;
        repos.set(`${owner}/${repo.name}`, repo);
      }
      return sendJson(res, 200, repoJson(repo, base));
    }
    if (method === 'DELETE') {
      repos.delete(`${owner}/${name}`);
      res.writeHead(204, { 'x-github-request-id': `req-${(requestSeq += 1)}` });
      return res.end();
    }
    return sendError(res, 404, 'Not Found');
  }

  // Branches
  if (rest[0] === 'branches') {
    if (rest.length === 1 && method === 'GET') {
      const list = [...repo.refs.entries()]
        .filter(([ref]) => ref.startsWith('refs/heads/'))
        .map(([ref, sha]) => ({ name: ref.slice(11), commit: { sha }, protected: false }))
        .sort((a, b) => (a.name < b.name ? -1 : 1));
      return sendJson(res, 200, list);
    }
    if (rest.length >= 2 && method === 'GET') {
      const branch = rest.slice(1).join('/');
      const sha = branchTip(repo, branch);
      if (!sha) return sendError(res, 404, 'Not Found');
      return sendJson(res, 200, { name: branch, commit: { sha }, protected: false });
    }
    return sendError(res, 404, 'Not Found');
  }

  // Commits
  if (rest[0] === 'commits' && rest.length === 1 && method === 'GET') {
    const wanted = query.get('sha');
    let tip = null;
    if (wanted) tip = branchTip(repo, wanted) || (getObject(repo, wanted) ? wanted : null);
    if (!tip) tip = branchTip(repo, repo.defaultBranch);
    if (!tip) return sendJson(res, 200, []);
    const history = historyFrom(repo, peelToCommit(repo, tip) || tip);
    return sendJson(res, 200, applyPagination(req, res, history).map((sha) => commitJson(repo, sha)));
  }

  // Git data refs
  if (rest[0] === 'git' && rest[1] === 'refs') {
    if (rest.length === 2 && method === 'POST') {
      const data = needBody();
      if (data === undefined) return;
      const ref = data.ref;
      const sha = data.sha;
      if (typeof ref !== 'string' || typeof sha !== 'string') return sendError(res, 422, 'Validation Failed');
      if (!getObject(repo, sha)) return sendError(res, 422, 'Validation Failed: unknown object');
      if (repo.refs.has(ref)) return sendError(res, 422, 'Reference already exists');
      repo.refs.set(ref, sha);
      repo.refsVersion += 1;
      return sendJson(res, 201, { ref, object: { sha, type: getObject(repo, sha)[0] } });
    }
    if (rest.length >= 3 && method === 'GET') {
      const ref = `refs/${rest.slice(2).join('/')}`;
      const sha = repo.refs.get(ref);
      if (!sha) return sendError(res, 404, 'Not Found');
      return sendJson(res, 200, { ref, object: { sha, type: getObject(repo, sha)[0] } });
    }
    return sendError(res, 404, 'Not Found');
  }

  // Contents
  if (rest[0] === 'contents') {
    const pathSegments = rest.slice(1);
    const path = pathSegments.join('/');
    if (method === 'GET') {
      const refParam = query.get('ref');
      let tip = null;
      if (refParam) tip = branchTip(repo, refParam) || (getObject(repo, refParam) ? refParam : null);
      if (!tip) tip = branchTip(repo, repo.defaultBranch);
      if (!tip) return sendError(res, 404, 'Not Found');
      const commit = parseCommit(getObject(repo, peelToCommit(repo, tip))[1]);
      if (path === '') return sendJson(res, 200, dirListing(repo, commit.tree, ''));
      const found = treeEntryAt(repo, commit.tree, pathSegments);
      if (!found) return sendError(res, 404, 'Not Found');
      if (found.kind === 'dir') return sendJson(res, 200, dirListing(repo, found.sha, path));
      const blob = getObject(repo, found.sha);
      return sendJson(res, 200, {
        type: 'file',
        encoding: 'base64',
        content: blob[1].toString('base64'),
        name: pathSegments[pathSegments.length - 1],
        path,
        sha: found.sha,
        size: found.size,
      });
    }
    if (method === 'PUT') {
      const data = needBody();
      if (data === undefined) return;
      if (typeof data.content !== 'string') return sendError(res, 422, 'Validation Failed: content is required');
      const branch = typeof data.branch === 'string' && data.branch !== '' ? data.branch : repo.defaultBranch;
      const existingTip = branchTip(repo, branch) || branchTip(repo, repo.defaultBranch);
      const existingFlat = commitTreeFlat(repo, existingTip ? peelToCommit(repo, existingTip) : null);
      const existing = existingFlat.get(path);
      if (data.sha !== undefined && (!existing || existing.oid !== data.sha)) {
        return sendError(res, 409, 'Conflict: the sha does not match the current blob');
      }
      const blobSha = storeObject(repo, 'blob', Buffer.from(String(data.content).replace(/\s/g, ''), 'base64'));
      const commit = commitFileChange(repo, branch, path, blobSha, data.message || '');
      return sendJson(res, existing ? 200 : 201, {
        content: { name: pathSegments[pathSegments.length - 1], path, sha: blobSha, size: getObject(repo, blobSha)[1].length, type: 'file', encoding: 'base64' },
        commit: { sha: commit },
      });
    }
    if (method === 'DELETE') {
      const data = needBody();
      if (data === undefined) return;
      const branch = typeof data.branch === 'string' && data.branch !== '' ? data.branch : repo.defaultBranch;
      const tip = branchTip(repo, branch);
      const flat = commitTreeFlat(repo, tip ? peelToCommit(repo, tip) : null);
      const existing = flat.get(path);
      if (!existing) return sendError(res, 404, 'Not Found');
      if (data.sha !== undefined && existing.oid !== data.sha) return sendError(res, 409, 'Conflict: the sha does not match the current blob');
      const commit = commitFileChange(repo, branch, path, null, data.message || '');
      return sendJson(res, 200, { content: null, commit: { sha: commit } });
    }
    return sendError(res, 404, 'Not Found');
  }

  // Labels
  if (rest[0] === 'labels' && rest.length === 1) {
    if (method === 'GET') return sendJson(res, 200, [...repo.labels.values()].map(labelJson));
    if (method === 'POST') {
      const data = needBody();
      if (data === undefined) return;
      if (typeof data.name !== 'string' || data.name === '') return sendError(res, 422, 'Validation Failed: name is required');
      if (repo.labels.has(data.name)) return sendError(res, 422, 'Validation Failed: name has already been taken');
      const label = { id: nextLabelId++, name: data.name, color: typeof data.color === 'string' ? data.color : 'ededed', description: data.description || '' };
      repo.labels.set(label.name, label);
      return sendJson(res, 201, labelJson(label));
    }
    return sendError(res, 404, 'Not Found');
  }

  // Issues
  if (rest[0] === 'issues') {
    if (rest.length === 1) {
      if (method === 'GET') {
        const state = query.get('state') || 'open';
        let list = [...repo.entries.values()].filter((entry) => !entry.pull);
        if (state !== 'all') list = list.filter((entry) => entry.state === state);
        const direction = query.get('direction') || 'desc';
        list.sort((a, b) => (direction === 'asc' ? a.seq - b.seq : b.seq - a.seq));
        return sendJson(res, 200, applyPagination(req, res, list).map((entry) => issueJson(repo, entry, base)));
      }
      if (method === 'POST') {
        const data = needBody();
        if (data === undefined) return;
        const labelNames = [];
        if (Array.isArray(data.labels)) {
          for (const label of data.labels) {
            const labelName = typeof label === 'string' ? label : label && label.name;
            if (typeof labelName !== 'string' || !repo.labels.has(labelName)) {
              return sendError(res, 422, `Validation Failed: label "${String(labelName)}" does not exist`);
            }
            labelNames.push(labelName);
          }
        }
        const entry = createEntry(repo, { title: data.title, body: data.body, labels: labelNames });
        return sendJson(res, 201, issueJson(repo, entry, base));
      }
      return sendError(res, 404, 'Not Found');
    }
    const number = parseInt(rest[1], 10);
    const entry = Number.isFinite(number) ? repo.entries.get(number) : undefined;
    if (rest.length === 2) {
      if (!entry) return sendError(res, 404, 'Not Found');
      if (method === 'GET') {
        // The read workload GETs one issue thousands of times; the body is a
        // pure function of the entry (labels are immutable once created), so
        // serve the serialized body cached under the entry's revision.
        const cacheKey = `${entry.rev}|${base}`;
        if (entry._jsonKey === cacheKey) return sendJsonBody(res, 200, entry._jsonBody);
        const body = Buffer.from(JSON.stringify(issueJson(repo, entry, base)), 'utf8');
        entry._jsonKey = cacheKey;
        entry._jsonBody = body;
        return sendJsonBody(res, 200, body);
      }
      if (method === 'PATCH') {
        const data = needBody();
        if (data === undefined) return;
        if (typeof data.state === 'string') entry.state = data.state;
        if (typeof data.title === 'string') entry.title = data.title;
        if (typeof data.body === 'string') entry.body = data.body;
        entry.rev += 1;
        return sendJson(res, 200, issueJson(repo, entry, base));
      }
      return sendError(res, 404, 'Not Found');
    }
    if (rest.length === 3 && rest[2] === 'comments') {
      if (!entry) return sendError(res, 404, 'Not Found');
      if (method === 'GET') return sendJson(res, 200, entry.comments.map(commentJson));
      if (method === 'POST') {
        const data = needBody();
        if (data === undefined) return;
        const comment = { id: nextCommentId++, body: typeof data.body === 'string' ? data.body : '' };
        entry.comments.push(comment);
        entry.rev += 1;
        return sendJson(res, 201, commentJson(comment));
      }
      return sendError(res, 404, 'Not Found');
    }
    return sendError(res, 404, 'Not Found');
  }

  // Pull requests
  if (rest[0] === 'pulls') {
    if (rest.length === 1) {
      if (method === 'GET') {
        const state = query.get('state') || 'open';
        let list = [...repo.entries.values()].filter((entry) => entry.pull);
        if (state !== 'all') list = list.filter((entry) => entry.state === state);
        list.sort((a, b) => b.seq - a.seq);
        return sendJson(res, 200, applyPagination(req, res, list).map((entry) => pullJson(repo, entry, base)));
      }
      if (method === 'POST') {
        const data = needBody();
        if (data === undefined) return;
        const normalizeRef = (value) => {
          let ref = typeof value === 'string' ? value : '';
          if (ref.includes(':')) ref = ref.slice(ref.lastIndexOf(':') + 1);
          if (ref.startsWith('refs/heads/')) ref = ref.slice(11);
          return ref;
        };
        const head = normalizeRef(data.head);
        const baseName = normalizeRef(data.base) || repo.defaultBranch;
        if (!head || !branchTip(repo, head)) return sendError(res, 422, 'Validation Failed: head branch does not exist');
        if (!branchTip(repo, baseName)) return sendError(res, 422, 'Validation Failed: base branch does not exist');
        if (head === baseName) return sendError(res, 422, 'Validation Failed: head and base are the same');
        const duplicate = [...repo.entries.values()].find(
          (candidate) => candidate.pull && candidate.state === 'open' && candidate.pull.headRef === head && candidate.pull.baseRef === baseName,
        );
        if (duplicate) return sendError(res, 422, 'Validation Failed: a pull request already exists for this head and base');
        const entry = createEntry(repo, {
          title: data.title,
          body: data.body,
          pull: {
            headRef: head,
            baseRef: baseName,
            headSha: branchTip(repo, head),
            baseSha: branchTip(repo, baseName),
            merged: false,
            mergeCommitSha: null,
          },
        });
        return sendJson(res, 201, pullJson(repo, entry, base));
      }
      return sendError(res, 404, 'Not Found');
    }
    const number = parseInt(rest[1], 10);
    const entry = Number.isFinite(number) ? repo.entries.get(number) : undefined;
    if (!entry || !entry.pull) {
      if (rest[2] === 'merge' && method === 'PUT') return sendError(res, 404, 'Not Found');
      return sendError(res, 404, 'Not Found');
    }
    if (rest.length === 2 && method === 'GET') return sendJson(res, 200, pullJson(repo, entry, base));
    if (rest.length === 3 && rest[2] === 'files' && method === 'GET') {
      return sendJson(res, 200, applyPagination(req, res, pullFiles(repo, entry)));
    }
    if (rest.length === 3 && rest[2] === 'merge' && method === 'PUT') {
      if (entry.pull.merged) return sendError(res, 405, 'Pull Request is not mergeable: already merged');
      const result = mergeEntry(repo, entry);
      if (result.error) return sendError(res, 405, 'Pull Request is not mergeable: conflict');
      return sendJson(res, 200, { sha: result.sha, merged: true, message: 'Pull Request successfully merged' });
    }
    return sendError(res, 404, 'Not Found');
  }

  return sendError(res, 404, 'Not Found');
}

// ---------------------------------------------------------------------------
// GraphQL v4 (the subset gh and github-mcp-server speak)
const GQL_TYPE_FIELDS = {
  Query: ['viewer', 'repository', 'node', 'search', 'rateLimit'],
  Mutation: ['createIssue', 'closeIssue', 'createPullRequest', 'mergePullRequest', 'addComment'],
  Repository: [
    'id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission',
    'hasIssuesEnabled', 'hasWikiEnabled', 'isPrivate', 'description', 'issue', 'issues',
    'pullRequest', 'pullRequests', 'createdAt', 'updatedAt', 'url', 'viewerCanAdminister',
  ],
  Issue: [
    'id', 'number', 'title', 'state', 'body', 'author', 'repository', 'labels', 'comments',
    'createdAt', 'updatedAt', 'closedAt', 'closed', 'url', 'stateReason',
  ],
  PullRequest: [
    'id', 'number', 'title', 'body', 'state', 'merged', 'mergeable', 'headRefName', 'baseRefName',
    'headRef', 'baseRef', 'files', 'author', 'repository', 'createdAt', 'updatedAt', 'mergedAt',
    'mergeCommit', 'additions', 'deletions', 'changedFiles', 'closed', 'isDraft',
  ],
  User: ['id', 'login', 'name', 'email', 'avatarUrl', 'url', 'createdAt'],
  Organization: ['id', 'login', 'name', 'email', 'avatarUrl', 'url'],
  Label: ['id', 'name', 'color', 'description'],
  IssueComment: ['id', 'body', 'author', 'createdAt', 'updatedAt', 'url'],
  Ref: ['name', 'prefix', 'target'],
  Commit: ['id', 'oid', 'message', 'authoredDate'],
  IssueConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestChangedFile: ['path', 'additions', 'deletions', 'changeType'],
  PullRequestChangedFileConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PageInfo: ['hasNextPage', 'hasPreviousPage', 'startCursor', 'endCursor'],
  CreateIssuePayload: ['issue', 'clientMutationId'],
  CloseIssuePayload: ['issue', 'clientMutationId'],
  CreatePullRequestPayload: ['pullRequest', 'clientMutationId'],
  MergePullRequestPayload: ['pullRequest', 'clientMutationId'],
  AddCommentPayload: ['commentEdge', 'subject', 'clientMutationId'],
  IssueEdge: ['node', 'cursor'],
  PullRequestEdge: ['node', 'cursor'],
  CommentEdge: ['node', 'cursor'],
  __Type: ['name', 'kind', 'description', 'fields', 'enumValues', 'possibleTypes', 'inputFields', 'ofType', 'specifiedByURL'],
  __Field: ['name', 'description', 'args', 'type', 'isDeprecated', 'deprecationReason'],
  __EnumValue: ['name', 'description', 'isDeprecated', 'deprecationReason'],
  __InputValue: ['name', 'description', 'type', 'defaultValue'],
  __Schema: ['types', 'queryType', 'mutationType', 'subscriptionType', 'directives'],
  __Directive: ['name', 'description', 'locations', 'args'],
};
const GQL_ENUMS = {
  SearchType: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION'],
  IssueState: ['OPEN', 'CLOSED'],
  PullRequestState: ['OPEN', 'CLOSED', 'MERGED'],
  MergeableState: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'],
  RepositoryPermission: ['ADMIN', 'MAINTAIN', 'WRITE', 'TRIAGE', 'READ'],
  OrderDirection: ['ASC', 'DESC'],
  IssueOrderField: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'],
  PullRequestMergeMethod: ['MERGE', 'SQUASH', 'REBASE'],
  __TypeKind: ['SCALAR', 'OBJECT', 'INTERFACE', 'UNION', 'ENUM', 'INPUT_OBJECT', 'LIST', 'NON_NULL'],
};
function gqlTokenize(source) {
  const tokens = [];
  let i = 0;
  const isNameStart = (c) => /[A-Za-z_]/.test(c);
  const isNameChar = (c) => /[A-Za-z0-9_]/.test(c);
  while (i < source.length) {
    const c = source[i];
    if (c === '#') {
      while (i < source.length && source[i] !== '\n') i += 1;
      continue;
    }
    if (/\s|,/.test(c)) {
      i += 1;
      continue;
    }
    if (source.startsWith('...', i)) {
      tokens.push({ kind: '...' });
      i += 3;
      continue;
    }
    if ('{}()[]:=@$|!&'.includes(c)) {
      tokens.push({ kind: c });
      i += 1;
      continue;
    }
    if (c === '"') {
      if (source.startsWith('"""', i)) {
        const end = source.indexOf('"""', i + 3);
        tokens.push({ kind: 'string', value: source.slice(i + 3, end === -1 ? source.length : end) });
        i = end === -1 ? source.length : end + 3;
        continue;
      }
      let j = i + 1;
      let value = '';
      while (j < source.length && source[j] !== '"') {
        if (source[j] === '\\') {
          const esc = source[j + 1];
          value += esc === 'n' ? '\n' : esc === 't' ? '\t' : esc === 'r' ? '\r' : esc === 'b' ? '\b' : esc === 'f' ? '\f' : esc === '/' ? '/' : esc === '\\' ? '\\' : esc === '"' ? '"' : esc;
          j += 2;
        } else {
          value += source[j];
          j += 1;
        }
      }
      tokens.push({ kind: 'string', value });
      i = j + 1;
      continue;
    }
    if (/[0-9-]/.test(c)) {
      let j = i;
      let value = '';
      while (j < source.length && /[0-9.eE+-]/.test(source[j])) {
        value += source[j];
        j += 1;
      }
      tokens.push({ kind: 'number', value });
      i = j;
      continue;
    }
    if (isNameStart(c)) {
      let j = i;
      let value = '';
      while (j < source.length && isNameChar(source[j])) {
        value += source[j];
        j += 1;
      }
      tokens.push({ kind: 'name', value });
      i = j;
      continue;
    }
    throw new Error(`unexpected character ${JSON.stringify(c)} in GraphQL document`);
  }
  return tokens;
}
function gqlParse(source) {
  const tokens = gqlTokenize(source);
  let pos = 0;
  const peek = () => tokens[pos];
  const next = () => tokens[(pos += 1) - 1];
  const expect = (kind) => {
    const token = next();
    if (!token || token.kind !== kind) throw new Error(`expected ${kind} in GraphQL document`);
    return token;
  };
  function parseValue() {
    const token = next();
    if (!token) throw new Error('unexpected end of document');
    if (token.kind === '$') return { var: expect('name').value };
    if (token.kind === 'string') return token.value;
    if (token.kind === 'number') return token.value.includes('.') || token.value.includes('e') || token.value.includes('E') ? parseFloat(token.value) : parseInt(token.value, 10);
    if (token.kind === 'name') {
      if (token.value === 'true') return true;
      if (token.value === 'false') return false;
      if (token.value === 'null') return null;
      return { enum: token.value };
    }
    if (token.kind === '[') {
      const list = [];
      while (peek() && peek().kind !== ']') list.push(parseValue());
      expect(']');
      return list;
    }
    if (token.kind === '{') {
      const object = {};
      while (peek() && peek().kind !== '}') {
        const key = expect('name').value;
        expect(':');
        object[key] = parseValue();
      }
      expect('}');
      return object;
    }
    throw new Error('unexpected value in GraphQL document');
  }
  function parseSelectionSet() {
    expect('{');
    const selections = [];
    while (peek() && peek().kind !== '}') selections.push(parseSelection());
    expect('}');
    return selections;
  }
  function parseSelection() {
    if (peek().kind === '...') {
      next();
      const onToken = next();
      if (onToken.kind === 'name' && onToken.value === 'on') {
        const typeCondition = expect('name').value;
        return { fragment: typeCondition, selections: parseSelectionSet() };
      }
      return { spread: onToken.value };
    }
    let name = expect('name').value;
    let alias = null;
    if (peek() && peek().kind === ':') {
      next();
      alias = name;
      name = expect('name').value;
    }
    const args = {};
    if (peek() && peek().kind === '(') {
      next();
      while (peek() && peek().kind !== ')') {
        const key = expect('name').value;
        expect(':');
        args[key] = parseValue();
      }
      expect(')');
    }
    // Directives are parsed and ignored.
    while (peek() && peek().kind === '@') {
      next();
      expect('name');
      if (peek() && peek().kind === '(') {
        next();
        while (peek() && peek().kind !== ')') {
          expect('name');
          expect(':');
          parseValue();
        }
        expect(')');
      }
    }
    let selections = null;
    if (peek() && peek().kind === '{') selections = parseSelectionSet();
    return { name, alias, args, selections };
  }
  function parseTypeRef() {
    if (peek().kind === '[') {
      next();
      parseTypeRef();
      expect(']');
    } else {
      expect('name');
    }
    if (peek() && peek().kind === '!') next();
  }
  const operations = [];
  const fragments = {};
  while (pos < tokens.length) {
    const token = peek();
    if (token.kind === '{') {
      operations.push({ type: 'query', name: null, varDefs: {}, selections: parseSelectionSet() });
      continue;
    }
    if (token.kind === 'name' && (token.value === 'query' || token.value === 'mutation' || token.value === 'subscription')) {
      next();
      let opName = null;
      const varDefs = {};
      if (peek() && peek().kind === 'name') opName = next().value;
      if (peek() && peek().kind === '(') {
        next();
        while (peek() && peek().kind !== ')') {
          expect('$');
          const varName = expect('name').value;
          expect(':');
          parseTypeRef();
          if (peek() && peek().kind === '=') {
            next();
            varDefs[varName] = parseValue();
          } else varDefs[varName] = undefined;
        }
        expect(')');
      }
      operations.push({ type: token.value, name: opName, varDefs, selections: parseSelectionSet() });
      continue;
    }
    if (token.kind === 'name' && token.value === 'fragment') {
      next();
      const fragName = expect('name').value;
      expect('name'); // 'on'
      const typeCondition = expect('name').value;
      fragments[fragName] = { typeCondition, selections: parseSelectionSet() };
      continue;
    }
    throw new Error('unsupported GraphQL document structure');
  }
  return { operations, fragments };
}
function gqlResolveValue(value, variables) {
  if (value === null || value === undefined) return value;
  if (Array.isArray(value)) return value.map((item) => gqlResolveValue(item, variables));
  if (typeof value === 'object') {
    if ('var' in value) return variables[value.var];
    if ('enum' in value) return value.enum;
    const out = {};
    for (const [key, item] of Object.entries(value)) out[key] = gqlResolveValue(item, variables);
    return out;
  }
  return value;
}

function gqlNode(type, fields) {
  return { __t: type, ...fields };
}
function gqlCursor(offset) {
  return Buffer.from(`cursor:${offset}`, 'utf8').toString('base64');
}
function gqlCursorOffset(cursor) {
  try {
    const text = Buffer.from(String(cursor), 'base64').toString('utf8');
    const match = /^cursor:(\d+)$/.exec(text);
    return match ? Number(match[1]) : 0;
  } catch {
    return 0;
  }
}
function findRepoById(id) {
  for (const repo of repos.values()) if (repo.id === id) return repo;
  return null;
}
function findEntryByGlobalId(parsed) {
  const numeric = Number(parsed.key);
  if (!Number.isFinite(numeric)) return null;
  for (const repo of repos.values()) {
    for (const entry of repo.entries.values()) {
      if (entry.id === numeric) return { repo, entry };
    }
  }
  return null;
}
function gqlConnection(items, args, nodeType) {
  const ordered = items;
  let start = 0;
  if (args && args.after !== undefined && args.after !== null) start = gqlCursorOffset(args.after) + 1;
  const first = args && typeof args.first === 'number' ? args.first : 100;
  const slice = ordered.slice(start, start + first);
  const hasNext = start + slice.length < ordered.length;
  const connection = {
    __t: nodeType,
    nodesRaw: slice,
    edgesRaw: slice.map((node, index) => gqlNode('Edge', { node, cursor: gqlCursor(start + index) })),
    pageInfo: gqlNode('PageInfo', {
      hasNextPage: hasNext,
      hasPreviousPage: start > 0,
      startCursor: slice.length ? gqlCursor(start) : null,
      endCursor: slice.length ? gqlCursor(start + slice.length - 1) : null,
    }),
    totalCount: ordered.length,
  };
  return connection;
}
function gqlResolveField(type, source, field, args, ctx) {
  // Plain-object fallback: payloads, connections, introspection leaves.
  if (type === 'PageInfo' || type.endsWith('Payload') || type.endsWith('Edge') || type === '__Field' || type === '__EnumValue' || type === '__InputValue') {
    return source[field] === undefined ? null : source[field];
  }
  switch (type) {
    case 'Query': {
      if (field === 'viewer') return ctx.viewerNode;
      if (field === 'repository') {
        const repo = args.owner === VIEWER.login ? getRepo(args.owner, args.name) : null;
        return repo ? gqlNode('Repository', { repo }) : null;
      }
      if (field === 'node') {
        const parsed = parseGlobalId(args.id);
        if (!parsed) return null;
        if (parsed.type === 'Repository') {
          const repo = findRepoById(Number(parsed.key));
          return repo ? gqlNode('Repository', { repo }) : null;
        }
        if (parsed.type === 'User') return ctx.viewerNode;
        if (parsed.type === 'Issue' || parsed.type === 'PullRequest') {
          const found = findEntryByGlobalId(parsed);
          if (!found) return null;
          return found.entry.pull ? gqlNode('PullRequest', found) : gqlNode('Issue', found);
        }
        return null;
      }
      if (field === '__type') {
        const name = args.name;
        if (GQL_TYPE_FIELDS[name] || GQL_ENUMS[name]) return gqlNode('__Type', { typeName: name });
        return null;
      }
      if (field === '__schema') return gqlNode('__Schema', {});
      return null;
    }
    case 'Mutation': {
      if (field === 'createIssue') {
        const input = args.input || {};
        const parsed = parseGlobalId(input.repositoryId);
        const repo = parsed ? findRepoById(Number(parsed.key)) : null;
        if (!repo) throw new Error('repository not found');
        const entry = createEntry(repo, { title: input.title, body: input.body });
        return gqlNode('CreateIssuePayload', { issue: gqlNode('Issue', { repo, entry }), clientMutationId: input.clientMutationId || null });
      }
      if (field === 'closeIssue') {
        const input = args.input || {};
        const parsed = parseGlobalId(input.issueId);
        const found = parsed ? findEntryByGlobalId(parsed) : null;
        if (!found) throw new Error('issue not found');
        found.entry.state = 'closed';
        found.entry.rev += 1;
        return gqlNode('CloseIssuePayload', { issue: gqlNode('Issue', found), clientMutationId: input.clientMutationId || null });
      }
      if (field === 'createPullRequest') {
        const input = args.input || {};
        const parsed = parseGlobalId(input.repositoryId);
        const repo = parsed ? findRepoById(Number(parsed.key)) : null;
        if (!repo) throw new Error('repository not found');
        const normalize = (value) => {
          let ref = typeof value === 'string' ? value : '';
          if (ref.startsWith('refs/heads/')) ref = ref.slice(11);
          return ref;
        };
        const head = normalize(input.headRefName);
        const baseName = normalize(input.baseRefName) || repo.defaultBranch;
        if (!branchTip(repo, head)) throw new Error('head branch does not exist');
        const entry = createEntry(repo, {
          title: input.title,
          body: input.body,
          pull: { headRef: head, baseRef: baseName, headSha: branchTip(repo, head), baseSha: branchTip(repo, baseName), merged: false, mergeCommitSha: null },
        });
        return gqlNode('CreatePullRequestPayload', { pullRequest: gqlNode('PullRequest', { repo, entry }), clientMutationId: input.clientMutationId || null });
      }
      if (field === 'mergePullRequest') {
        const input = args.input || {};
        const parsed = parseGlobalId(input.pullRequestId);
        const found = parsed ? findEntryByGlobalId(parsed) : null;
        if (!found || !found.entry.pull) throw new Error('pull request not found');
        const result = mergeEntry(found.repo, found.entry);
        if (result.error) throw new Error('Pull Request is not mergeable');
        return gqlNode('MergePullRequestPayload', { pullRequest: gqlNode('PullRequest', found), clientMutationId: input.clientMutationId || null });
      }
      if (field === 'addComment') {
        const input = args.input || {};
        const parsed = parseGlobalId(input.subjectId);
        const found = parsed ? findEntryByGlobalId(parsed) : null;
        if (!found) throw new Error('subject not found');
        const comment = { id: nextCommentId++, body: typeof input.body === 'string' ? input.body : '' };
        found.entry.comments.push(comment);
        found.entry.rev += 1;
        return gqlNode('AddCommentPayload', {
          commentEdge: gqlNode('CommentEdge', { node: gqlNode('IssueComment', { comment }), cursor: gqlCursor(comment.id) }),
          subject: gqlNode('Issue', found),
          clientMutationId: input.clientMutationId || null,
        });
      }
      return null;
    }
    case 'Repository': {
      const repo = source.repo;
      switch (field) {
        case 'id': return globalId('Repository', repo.id);
        case 'databaseId': return repo.id;
        case 'name': return repo.name;
        case 'nameWithOwner': return `${repo.owner}/${repo.name}`;
        case 'owner': return ctx.viewerNode;
        case 'defaultBranchRef': return repo.refs.has(`refs/heads/${repo.defaultBranch}`) ? gqlNode('Ref', { name: repo.defaultBranch }) : null;
        case 'viewerPermission': return 'ADMIN';
        case 'hasIssuesEnabled': return true;
        case 'hasWikiEnabled': return false;
        case 'isPrivate': return repo.private;
        case 'description': return repo.description;
        case 'createdAt':
        case 'updatedAt': return NOW_ISO;
        case 'url': return `${ctx.base}/${repo.owner}/${repo.name}`;
        case 'viewerCanAdminister': return true;
        case 'issue': {
          const entry = repo.entries.get(args.number);
          return entry ? gqlNode('Issue', { repo, entry }) : null;
        }
        case 'issues': {
          let list = [...repo.entries.values()].filter((entry) => !entry.pull);
          if (Array.isArray(args.states) && args.states.length) {
            const wanted = args.states.map((state) => String(state).toLowerCase());
            list = list.filter((entry) => wanted.includes(entry.state));
          }
          const direction = args.orderBy && args.orderBy.direction ? String(args.orderBy.direction) : 'DESC';
          const field2 = args.orderBy && args.orderBy.field ? String(args.orderBy.field) : 'CREATED_AT';
          list.sort((a, b) => {
            const ka = field2 === 'COMMENTS' ? a.comments.length : a.seq;
            const kb = field2 === 'COMMENTS' ? b.comments.length : b.seq;
            return direction === 'ASC' ? ka - kb : kb - ka;
          });
          return gqlConnection(list.map((entry) => gqlNode('Issue', { repo, entry })), args, 'IssueConnection');
        }
        case 'pullRequests': {
          let list = [...repo.entries.values()].filter((entry) => entry.pull);
          if (Array.isArray(args.states) && args.states.length) {
            const wanted = args.states.map((state) => String(state).toUpperCase());
            list = list.filter((entry) => wanted.includes(entry.pull.merged ? 'MERGED' : entry.state.toUpperCase()));
          }
          list.sort((a, b) => b.seq - a.seq);
          return gqlConnection(list.map((entry) => gqlNode('PullRequest', { repo, entry })), args, 'PullRequestConnection');
        }
        case 'pullRequest': {
          const entry = repo.entries.get(args.number);
          return entry && entry.pull ? gqlNode('PullRequest', { repo, entry }) : null;
        }
        default: return null;
      }
    }
    case 'Issue': {
      const { repo, entry } = source;
      switch (field) {
        case 'id': return globalId('Issue', entry.id);
        case 'number': return entry.number;
        case 'title': return entry.title;
        case 'body': return entry.body;
        case 'state': return entry.state.toUpperCase();
        case 'closed': return entry.state === 'closed';
        case 'author': return ctx.viewerNode;
        case 'repository': return gqlNode('Repository', { repo });
        case 'labels': return entry.labels.map((name) => gqlNode('Label', { name, color: (repo.labels.get(name) || {}).color || 'ededed', description: '' }));
        case 'comments': return gqlConnection(entry.comments.map((comment) => gqlNode('IssueComment', { comment })), args, 'IssueCommentConnection');
        case 'createdAt':
        case 'updatedAt': return NOW_ISO;
        case 'closedAt': return entry.state === 'closed' ? NOW_ISO : null;
        case 'url': return `${ctx.base}/${repo.owner}/${repo.name}/issues/${entry.number}`;
        case 'stateReason': return null;
        default: return null;
      }
    }
    case 'PullRequest': {
      const { repo, entry } = source;
      switch (field) {
        case 'id': return globalId('PullRequest', entry.id);
        case 'number': return entry.number;
        case 'title': return entry.title;
        case 'body': return entry.body;
        case 'state': return entry.pull.merged ? 'MERGED' : entry.state.toUpperCase();
        case 'merged': return entry.pull.merged;
        case 'mergeable': return pullMergeable(repo, entry);
        case 'headRefName': return entry.pull.headRef;
        case 'baseRefName': return entry.pull.baseRef;
        case 'headRef': return gqlNode('Ref', { name: entry.pull.headRef });
        case 'baseRef': return gqlNode('Ref', { name: entry.pull.baseRef });
        case 'files': {
          const files = pullFiles(repo, entry).map((file) =>
            gqlNode('PullRequestChangedFile', { path: file.filename, additions: file.additions, deletions: file.deletions, changeType: file.status.toUpperCase() }),
          );
          return gqlConnection(files, args, 'PullRequestChangedFileConnection');
        }
        case 'author': return ctx.viewerNode;
        case 'repository': return gqlNode('Repository', { repo });
        case 'createdAt':
        case 'updatedAt': return NOW_ISO;
        case 'mergedAt': return entry.pull.merged ? NOW_ISO : null;
        case 'mergeCommit': return entry.pull.mergeCommitSha ? gqlNode('Commit', { repo, sha: entry.pull.mergeCommitSha }) : null;
        case 'additions': return pullFiles(repo, entry).reduce((sum, file) => sum + file.additions, 0);
        case 'deletions': return pullFiles(repo, entry).reduce((sum, file) => sum + file.deletions, 0);
        case 'changedFiles': return pullFiles(repo, entry).length;
        case 'closed': return entry.state === 'closed';
        case 'isDraft': return false;
        default: return null;
      }
    }
    case 'User':
    case 'Organization': {
      switch (field) {
        case 'id': return globalId('User', VIEWER.id);
        case 'login': return VIEWER.login;
        case 'name': return VIEWER.name;
        case 'email': return VIEWER.email;
        case 'avatarUrl': return '';
        case 'url': return `${ctx.base}/${VIEWER.login}`;
        case 'createdAt': return NOW_ISO;
        default: return null;
      }
    }
    case 'Label': return source[field] === undefined ? null : source[field];
    case 'IssueComment': {
      const comment = source.comment;
      switch (field) {
        case 'id': return globalId('IssueComment', comment.id);
        case 'body': return comment.body;
        case 'author': return ctx.viewerNode;
        case 'createdAt':
        case 'updatedAt': return NOW_ISO;
        case 'url': return '';
        default: return null;
      }
    }
    case 'Ref': return field === 'name' ? source.name : null;
    case 'Commit': {
      if (field === 'oid') return source.sha;
      if (field === 'id') return globalId('Commit', source.sha);
      if (field === 'message') {
        const obj = getObject(source.repo, source.sha);
        return obj ? parseCommit(obj[1]).message : '';
      }
      return null;
    }
    case '__Type': {
      const name = source.typeName;
      switch (field) {
        case 'name': return name;
        case 'kind': return GQL_ENUMS[name] ? 'ENUM' : 'OBJECT';
        case 'description': return null;
        case 'fields': return GQL_ENUMS[name] ? null : (GQL_TYPE_FIELDS[name] || []).map((fieldName) => gqlNode('__Field', { name: fieldName, description: null, isDeprecated: false, deprecationReason: null }));
        case 'enumValues': return GQL_ENUMS[name] ? GQL_ENUMS[name].map((value) => gqlNode('__EnumValue', { name: value, description: null, isDeprecated: false, deprecationReason: null })) : null;
        case 'possibleTypes': return null;
        case 'inputFields': return null;
        case 'ofType': return null;
        default: return null;
      }
    }
    case '__Schema': {
      if (field === 'queryType') return gqlNode('__Type', { typeName: 'Query' });
      if (field === 'mutationType') return gqlNode('__Type', { typeName: 'Mutation' });
      if (field === 'types') return Object.keys({ ...GQL_TYPE_FIELDS, ...GQL_ENUMS }).map((typeName) => gqlNode('__Type', { typeName }));
      return null;
    }
    default:
      return source && typeof source === 'object' && field in source ? source[field] : null;
  }
}
function gqlExecuteSelectionSet(type, source, selections, ctx, errors) {
  const out = {};
  for (const selection of selections) {
    if (selection.fragment) {
      if (selection.fragment === type || selection.fragment === 'Node' || type === selection.fragment) {
        Object.assign(out, gqlExecuteSelectionSet(type, source, selection.selections, ctx, errors));
      }
      continue;
    }
    if (selection.spread) {
      const fragment = ctx.fragments[selection.spread];
      if (fragment) Object.assign(out, gqlExecuteSelectionSet(type, source, fragment.selections, ctx, errors));
      continue;
    }
    const key = selection.alias || selection.name;
    if (selection.name === '__typename') {
      out[key] = type;
      continue;
    }
    const fieldType = type;
    const knownFields = GQL_TYPE_FIELDS[fieldType];
    const isMeta = selection.name === '__type' || selection.name === '__schema';
    if (!isMeta && knownFields && !knownFields.includes(selection.name) && !(source && typeof source === 'object' && selection.name in source)) {
      errors.push({ message: `Field '${selection.name}' doesn't exist on type '${fieldType}'` });
      out[key] = null;
      continue;
    }
    let value;
    try {
      const args = {};
      for (const [argName, argValue] of Object.entries(selection.args)) args[argName] = gqlResolveValue(argValue, ctx.variables);
      value = gqlResolveField(fieldType, source, selection.name, args, ctx);
    } catch (error) {
      errors.push({ message: error.message });
      out[key] = null;
      continue;
    }
    out[key] = gqlCompleteValue(value, selection, ctx, errors);
  }
  return out;
}
function gqlCompleteValue(value, selection, ctx, errors) {
  if (value === null || value === undefined) return null;
  if (!selection.selections) return value;
  if (Array.isArray(value)) return value.map((item) => gqlCompleteValue(item, selection, ctx, errors));
  if (typeof value === 'object' && value.__t) {
    if (value.__t.endsWith('Connection')) {
      // Connections expose nodes/edges/pageInfo/totalCount.
      const connectionView = {
        __t: value.__t,
        nodes: value.nodesRaw,
        edges: value.edgesRaw,
        pageInfo: value.pageInfo,
        totalCount: value.totalCount,
      };
      return gqlExecuteSelectionSet(value.__t, connectionView, selection.selections, ctx, errors);
    }
    return gqlExecuteSelectionSet(value.__t, value, selection.selections, ctx, errors);
  }
  return value;
}
function gqlHandleOne(payload, ctx) {
  const errors = [];
  try {
    const document = gqlParse(typeof payload.query === 'string' ? payload.query : '');
    ctx.fragments = document.fragments;
    let operation = document.operations[0];
    if (payload.operationName) operation = document.operations.find((candidate) => candidate.name === payload.operationName) || operation;
    if (!operation) return { errors: [{ message: 'no operation in document' }] };
    ctx.variables = { ...(payload.variables || {}) };
    for (const [name, fallback] of Object.entries(operation.varDefs)) {
      if (ctx.variables[name] === undefined && fallback !== undefined) ctx.variables[name] = gqlResolveValue(fallback, ctx.variables);
    }
    const rootType = operation.type === 'mutation' ? 'Mutation' : 'Query';
    const data = gqlExecuteSelectionSet(rootType, {}, operation.selections, ctx, errors);
    const result = { data };
    if (errors.length) result.errors = errors;
    return result;
  } catch (error) {
    return { errors: [{ message: error.message }] };
  }
}

// ---------------------------------------------------------------------------
// MCP (JSON-RPC 2.0 over Streamable HTTP)
const MCP_TOOLS = [
  {
    name: 'create_repo',
    description: 'Create a new repository for the authenticated user.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'The repository name.' },
        description: { type: 'string', description: 'A short description of the repository.' },
        private: { type: 'boolean', description: 'Whether the repository is private.' },
      },
      required: ['name'],
    },
  },
  {
    name: 'get_repo',
    description: 'Get a repository by owner and name.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The issue title.' },
        body: { type: 'string', description: 'The issue body.' },
      },
      required: ['owner', 'repo', 'title'],
    },
  },
  {
    name: 'list_issues',
    description: 'List issues in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        state: { type: 'string', description: 'Filter by state: open, closed or all.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The pull request title.' },
        head: { type: 'string', description: 'The head branch.' },
        base: { type: 'string', description: 'The base branch.' },
        body: { type: 'string', description: 'The pull request body.' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request (squash).',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        pull_number: { type: 'number', description: 'The pull request number.' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
  },
];
function mcpToolResult(value) {
  return { content: [{ type: 'text', text: JSON.stringify(value) }], structuredContent: value, isError: false };
}
function mcpCallTool(name, args, base) {
  const tool = MCP_TOOLS.find((candidate) => candidate.name === name);
  if (!tool) return { rpcError: { code: -32601, message: `Method not found: ${name}` } };
  const missing = (tool.inputSchema.required || []).filter((key) => args[key] === undefined || args[key] === null || args[key] === '');
  if (missing.length) return { rpcError: { code: -32602, message: `Missing required argument(s): ${missing.join(', ')}` } };
  try {
    switch (name) {
      case 'create_repo': {
        if (getRepo(VIEWER.login, args.name)) return mcpToolResult(repoJson(getRepo(VIEWER.login, args.name), base));
        const repo = newRepo(VIEWER.login, args.name, args.description || '', args.private);
        repos.set(`${VIEWER.login}/${args.name}`, repo);
        return mcpToolResult(repoJson(repo, base));
      }
      case 'get_repo': {
        const repo = args.owner === VIEWER.login ? getRepo(args.owner, args.repo) : null;
        if (!repo) return { toolError: `repository ${args.owner}/${args.repo} not found` };
        return mcpToolResult(repoJson(repo, base));
      }
      case 'create_issue': {
        const repo = args.owner === VIEWER.login ? getRepo(args.owner, args.repo) : null;
        if (!repo) return { toolError: `repository ${args.owner}/${args.repo} not found` };
        const entry = createEntry(repo, { title: args.title, body: args.body });
        return mcpToolResult(issueJson(repo, entry, base));
      }
      case 'list_issues': {
        const repo = args.owner === VIEWER.login ? getRepo(args.owner, args.repo) : null;
        if (!repo) return { toolError: `repository ${args.owner}/${args.repo} not found` };
        const state = typeof args.state === 'string' ? args.state : 'open';
        let list = [...repo.entries.values()].filter((entry) => !entry.pull);
        if (state !== 'all') list = list.filter((entry) => entry.state === state);
        list.sort((a, b) => b.seq - a.seq);
        return mcpToolResult(list.map((entry) => issueJson(repo, entry, base)));
      }
      case 'create_pull_request': {
        const repo = args.owner === VIEWER.login ? getRepo(args.owner, args.repo) : null;
        if (!repo) return { toolError: `repository ${args.owner}/${args.repo} not found` };
        const normalize = (value) => {
          let ref = typeof value === 'string' ? value : '';
          if (ref.includes(':')) ref = ref.slice(ref.lastIndexOf(':') + 1);
          if (ref.startsWith('refs/heads/')) ref = ref.slice(11);
          return ref;
        };
        const head = normalize(args.head);
        const baseName = normalize(args.base) || repo.defaultBranch;
        if (!branchTip(repo, head)) return { toolError: `head branch ${head} does not exist` };
        const entry = createEntry(repo, {
          title: args.title,
          body: args.body,
          pull: { headRef: head, baseRef: baseName, headSha: branchTip(repo, head), baseSha: branchTip(repo, baseName), merged: false, mergeCommitSha: null },
        });
        return mcpToolResult(pullJson(repo, entry, base));
      }
      case 'merge_pull_request': {
        const repo = args.owner === VIEWER.login ? getRepo(args.owner, args.repo) : null;
        if (!repo) return { toolError: `repository ${args.owner}/${args.repo} not found` };
        const entry = repo.entries.get(Number(args.pull_number));
        if (!entry || !entry.pull) return { toolError: `pull request ${args.pull_number} not found` };
        const result = mergeEntry(repo, entry);
        if (result.error) return { toolError: 'Pull Request is not mergeable' };
        return mcpToolResult(pullJson(repo, entry, base));
      }
      default:
        return { rpcError: { code: -32601, message: `Method not found: ${name}` } };
    }
  } catch (error) {
    return { toolError: error.message };
  }
}
function handleMcp(req, res, body, base) {
  let parsed;
  try {
    parsed = JSON.parse(body.toString('utf8'));
  } catch {
    res.writeHead(400, { 'content-type': 'application/json' });
    res.end(JSON.stringify({ jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } }));
    return;
  }
  const respond = (id, result) => {
    res.writeHead(200, { 'content-type': 'application/json' });
    res.end(JSON.stringify({ jsonrpc: '2.0', id, result }));
  };
  const respondError = (id, code, message) => {
    res.writeHead(200, { 'content-type': 'application/json' });
    res.end(JSON.stringify({ jsonrpc: '2.0', id, error: { code, message } }));
  };
  const handleOne = (message) => {
    if (!message || typeof message !== 'object') return null;
    const { id, method, params } = message;
    const isNotification = id === undefined;
    switch (method) {
      case 'server/discover':
        return {
          id,
          result: {
            serverInfo: { name: 'forge', version: '1.0.0' },
            capabilities: { tools: {} },
            supportedVersions: ['2026-07-28', '2025-11-25', '2025-03-26'],
            protocolVersion: '2026-07-28',
          },
        };
      case 'initialize':
        return {
          id,
          result: {
            protocolVersion: params && typeof params.protocolVersion === 'string' ? params.protocolVersion : '2025-11-25',
            capabilities: { tools: {} },
            serverInfo: { name: 'forge', version: '1.0.0' },
          },
        };
      case 'ping':
        return { id, result: {} };
      case 'tools/list':
        return { id, result: { tools: MCP_TOOLS } };
      case 'tools/call': {
        const toolName = params && typeof params.name === 'string' ? params.name : '';
        const args = (params && params.arguments) || {};
        const outcome = mcpCallTool(toolName, args, base);
        if (outcome.rpcError) return { id, error: outcome.rpcError };
        if (outcome.toolError) return { id, result: { content: [{ type: 'text', text: outcome.toolError }], isError: true } };
        return { id, result: outcome };
      }
      default:
        if (isNotification) return null;
        return { id, error: { code: -32601, message: `Method not found: ${method}` } };
    }
  };
  if (Array.isArray(parsed)) {
    const results = parsed.map(handleOne).filter((item) => item !== null);
    res.writeHead(200, { 'content-type': 'application/json' });
    res.end(JSON.stringify(results));
    return;
  }
  const outcome = handleOne(parsed);
  if (outcome === null) {
    res.writeHead(202);
    res.end();
    return;
  }
  if (outcome.error) return respondError(outcome.id, outcome.error.code, outcome.error.message);
  return respond(outcome.id, outcome.result);
}

// ---------------------------------------------------------------------------
// Router and lifecycle
const EMPTY_BODY = Buffer.alloc(0);
// Split a request target into path and query without the WHATWG URL
// parser: it is one of the most expensive per-request calls in the
// dispatcher and everything it computed is reproduced here. The query
// is parsed lazily, only when a handler actually asks for a value, and
// the segment walk resolves dot segments the way the URL parser did.
function splitTarget(target) {
  let rest = target;
  const scheme = rest.indexOf('://');
  if (scheme >= 0) {
    const slash = rest.indexOf('/', scheme + 3);
    rest = slash >= 0 ? rest.slice(slash) : '/';
  }
  let queryString = '';
  const q = rest.indexOf('?');
  if (q >= 0) {
    queryString = rest.slice(q + 1);
    rest = rest.slice(0, q);
  }
  let params = null;
  const query = {
    get(name) {
      if (params === null) params = new URLSearchParams(queryString);
      return params.get(name);
    },
  };
  return { path: rest === '' ? '/' : rest, query };
}
function pathSegments(path) {
  const out = [];
  for (const raw of path.replace(/\\/g, '/').split('/')) {
    if (raw === '') continue;
    const segment = raw.includes('%') ? decodeURIComponent(raw) : raw;
    if (segment === '.') continue;
    if (segment === '..') {
      out.pop();
      continue;
    }
    out.push(segment);
  }
  return out;
}

const server = http.createServer(async (req, res) => {
  try {
    const { path, query } = splitTarget(req.url || '/');
    const base = `http://${req.headers.host || 'localhost'}`;
    if (path === '/healthz') {
      res.writeHead(200, { 'content-type': 'application/json' });
      res.end(JSON.stringify({ ok: true }));
      return;
    }
    // A request that declares no body is answered without putting the
    // stream machinery through a read cycle: waiting for its 'end'
    // event costs a full event-loop turn per request, which is the
    // read workload's whole budget. Bodies that do exist are read
    // exactly as before.
    const lengthHeader = req.headers['content-length'];
    const hasBody =
      req.headers['transfer-encoding'] !== undefined ||
      (lengthHeader !== undefined && lengthHeader !== '0');
    const body = hasBody ? await readBody(req) : EMPTY_BODY;
    if (!authed(req)) {
      sendError(res, 401, 'Bad credentials');
      return;
    }
    const segments = pathSegments(path);
    if (segments[0] === 'api' && segments[1] === 'v3') {
      handleRest(req, res, segments.slice(2), query, body, base);
      return;
    }
    if (path === '/api/graphql') {
      if (req.method !== 'POST') {
        sendError(res, 404, 'Not Found');
        return;
      }
      let payload;
      try {
        payload = JSON.parse(body.toString('utf8'));
      } catch {
        sendJson(res, 400, { errors: [{ message: 'invalid JSON' }] });
        return;
      }
      const ctx = { base, viewerNode: gqlNode('User', {}), variables: {}, fragments: {} };
      if (Array.isArray(payload)) {
        sendJson(res, 200, payload.map((item) => gqlHandleOne(item || {}, { ...ctx, variables: {}, fragments: {} })));
        return;
      }
      sendJson(res, 200, gqlHandleOne(payload || {}, ctx));
      return;
    }
    if (path === '/mcp') {
      if (req.method !== 'POST') {
        res.writeHead(405, { 'content-type': 'application/json' });
        res.end(JSON.stringify({ jsonrpc: '2.0', id: null, error: { code: -32601, message: 'Method not found' } }));
        return;
      }
      handleMcp(req, res, body, base);
      return;
    }
    // Git smart HTTP: /{owner}/{repo}.git/...
    if (segments.length >= 2 && segments[1].endsWith('.git')) {
      const owner = segments[0];
      const name = segments[1].slice(0, -4);
      const repo = owner === VIEWER.login ? getRepo(owner, name) : null;
      const service = query.get('service');
      if (segments.length === 3 && segments[2] === 'info' && req.method === 'GET') {
        // unreachable: 'info' and 'refs' are two segments; handled below
      }
      if (req.method === 'GET' && path.endsWith('/info/refs')) {
        const isV2 = (req.headers['git-protocol'] || '').includes('version=2');
        gitInfoRefs(req, res, repo, service === 'git-receive-pack' ? 'git-receive-pack' : 'git-upload-pack', isV2);
        return;
      }
      if (req.method === 'POST' && path.endsWith('/git-upload-pack')) {
        gitUploadPack(req, res, repo, body);
        return;
      }
      if (req.method === 'POST' && path.endsWith('/git-receive-pack')) {
        gitReceivePack(req, res, repo, body);
        return;
      }
      res.writeHead(404, { 'content-type': 'text/plain' });
      res.end('not found');
      return;
    }
    sendError(res, 404, 'Not Found');
  } catch (error) {
    try {
      if (!res.headersSent) sendError(res, 500, `internal error: ${error.message}`);
      else res.end();
    } catch {
      // connection already gone
    }
  }
});
// Responses here are small and latency-bound; Nagle's algorithm would
// hold each one back waiting to coalesce a second write that never
// comes, so turn it off on every accepted socket.
server.on('connection', (socket) => socket.setNoDelay(true));

const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));
async function registerWithEnv(port) {
  for (let attempt = 0; ; attempt += 1) {
    try {
      const response = await fetch(`${ENV_URL}/register`, {
        method: 'POST',
        headers: { 'content-type': 'application/json' },
        body: JSON.stringify({ port }),
        signal: AbortSignal.timeout(30000),
      });
      if (response.status === 200 || response.status === 409) return;
      if (response.status === 400 || response.status === 405) throw new Error(`register answered HTTP ${response.status}`);
    } catch (error) {
      if (error instanceof Error && error.message.startsWith('register answered')) throw error;
    }
    await sleep(Math.min(2000, 250 * 2 ** Math.min(attempt, 8)));
  }
}
async function waitForDone() {
  for (let attempt = 0; ; attempt += 1) {
    try {
      const response = await fetch(`${ENV_URL}/done`, { signal: AbortSignal.timeout(30000) });
      if (response.ok) {
        const body = await response.json();
        if (body && body.done === true) return;
      }
    } catch {
      // env not answering yet; keep polling
    }
    await sleep(Math.min(2000, 250 * 2 ** Math.min(attempt, 8)));
  }
}
async function main() {
  await new Promise((resolve, reject) => {
    server.once('error', reject);
    server.listen(0, () => resolve());
  });
  const address = server.address();
  process.stdout.write(`[entry] listening on port ${address.port}\n`);
  if (ENV_URL) {
    await registerWithEnv(address.port);
    process.stdout.write('[entry] registered; waiting for the env to say done\n');
    await waitForDone();
    server.close();
    process.stdout.write('[entry] done\n');
    process.exit(0);
  }
}
main().catch((error) => {
  process.stderr.write(`[entry] ${error instanceof Error ? error.message : String(error)}\n`);
  process.exit(1);
});
