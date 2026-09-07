"use strict";

const COLORS = {
  axiom: "#e06b5c",
  thm: "#5aa9e6",
  lemma: "#6dd6a1",
  param: "#c9a227",
  terminal: "#9aa3b5",
};

let DATA = null;
let state = { dataset: "human", root: null, view: "trie" };
let cy = null;

// ---- Metamath statement rendering (set.mm symbol + color scheme) ----
// wff-variable tokens render as their Greek glyph; setvar/class keep their token.
const GREEK = {
  ph: "φ", ps: "ψ", ch: "χ", th: "θ", ta: "τ", et: "η", ze: "ζ", si: "σ",
  rh: "ρ", mu: "μ", la: "λ", ka: "κ", al: "α", be: "β", ga: "γ", de: "δ",
  ep: "ε", io: "ι", ph0: "φ", ps0: "ψ",
};
// constant/operator tokens -> unicode (best-effort; unknown tokens pass through)
const SYM = {
  "->": "→", "-.": "¬", "A.": "∀", "E.": "∃", "<->": "↔", "/\\": "∧",
  "\\/": "∨", "e.": "∈", "e/": "∉", "C_": "⊆", "C.": "⊊", "=": "=",
  "=/=": "≠", "<": "<", "<_": "≤", "|-": "⊢", "E!": "∃!", "E*": "∃*",
  "u.": "∪", "i^i": "∩", "(/)": "∅", "X.": "×", "|->": "↦", "o.": "∘",
  "+": "+", "x.": "·", "-": "−", "/": "/", "^": "^", "<.": "⟨", ">.": "⟩",
  "{": "{", "}": "}", "(": "(", ")": ")", "[": "[", "]": "]", ",": ",",
  "|": "∣", "/-": "⊬", "\\/_": "⊻", "RR": "ℝ", "CC": "ℂ", "ZZ": "ℤ",
  "NN": "ℕ", "QQ": "ℚ", "0": "0", "1": "1", "2": "2", "3": "3",
  "A": "𝐴", "B": "𝐵", // overridden by vartypes when class vars
};

function vartype(tok) {
  return DATA && DATA.vartypes ? DATA.vartypes[tok] : undefined;
}

function mmToken(tok) {
  const vt = vartype(tok);
  if (vt) {
    const disp = vt === "wff" && GREEK[tok] ? GREEK[tok] : tok;
    return `<span class="v-${vt}">${escapeHtml(disp)}</span>`;
  }
  if (Object.prototype.hasOwnProperty.call(SYM, tok))
    return `<span class="op">${escapeHtml(SYM[tok])}</span>`;
  return `<span class="cn">${escapeHtml(tok)}</span>`;
}

// render a raw space-separated set.mm statement into colored Metamath HTML
function mmRender(stmt) {
  if (!stmt) return '<span class="cn">(no statement)</span>';
  const toks = String(stmt).trim().split(/\s+/);
  const body = toks.map(mmToken).join(" ");
  return `<span class="mm"><span class="turn">⊢</span>${body}</span>`;
}

// ---- term helpers (term json: {v:i} | {s:name, c:[...]}) ----
function termSize(t) {
  if (t.v !== undefined) return 0;
  return t.c.reduce((a, c) => a + 1 + termSize(c), 0);
}
function refNames(t, acc) {
  if (t.v !== undefined) return acc;
  acc.set(t.s, (acc.get(t.s) || 0) + 1);
  t.c.forEach((c) => refNames(c, acc));
  return acc;
}

function g() {
  return DATA[state.dataset];
}

// ---- reachable dependency DAG from a root ----
function reachable(root) {
  const G = g();
  const nodes = new Set();
  const edges = [];
  const seen = new Set();
  const stack = [root];
  while (stack.length) {
    const name = stack.pop();
    if (seen.has(name)) continue;
    seen.add(name);
    nodes.add(name);
    const prod = G.productions[name];
    if (!prod) continue; // terminal (axiom) -> leaf
    const refs = refNames(prod.rhs, new Map());
    refs.forEach((count, q) => {
      nodes.add(q);
      edges.push({ p: name, q, count });
      if (!seen.has(q)) stack.push(q);
    });
  }
  return { nodes, edges };
}

function nodeKind(name) {
  const info = g().info[name];
  return info ? info.kind : "terminal";
}

// ---- proof tree (fast HTML, lazy-expanded, Metamath-rendered) ----
// direct dependencies of a theorem = distinct names referenced in its
// production rhs, in first-occurrence (proof) order.
const _refCache = {};
function directRefs(name) {
  const key = state.dataset + ":" + name;
  if (_refCache[key]) return _refCache[key];
  const prod = g().productions[name];
  const order = [];
  if (prod) {
    const seen = new Set();
    (function walk(t) {
      if (t.v !== undefined) return;
      if (!seen.has(t.s)) { seen.add(t.s); order.push(t.s); }
      t.c.forEach(walk);
    })(prod.rhs);
  }
  _refCache[key] = order;
  return order;
}

function statementHtml(name) {
  const info = g().info[name] || {};
  return mmRender(info.statement || "");
}

// one <li> for a node; children built lazily on first expand
function makeTreeLi(name) {
  const li = document.createElement("li");
  const kids = directRefs(name);
  const node = document.createElement("div");
  node.className = "tnode";
  node.dataset.name = name;

  const tw = document.createElement("span");
  tw.className = "tw" + (kids.length ? "" : " leaf");
  tw.textContent = kids.length ? "▶" : "•";
  node.appendChild(tw);

  const dot = document.createElement("span");
  dot.className = "tdot k-" + nodeKind(name);
  node.appendChild(dot);

  const nm = document.createElement("span");
  nm.className = "tname k-" + nodeKind(name);
  nm.textContent = name;
  node.appendChild(nm);

  if (kids.length) {
    const cnt = document.createElement("span");
    cnt.className = "tcount";
    cnt.textContent = "(" + kids.length + ")";
    node.appendChild(cnt);
  }

  const st = document.createElement("span");
  st.className = "tstmt";
  st.innerHTML = statementHtml(name);
  node.appendChild(st);

  li.appendChild(node);

  const ul = document.createElement("ul");
  ul.style.display = "none";
  li.appendChild(ul);

  let built = false;
  const expand = () => {
    if (kids.length === 0) return;
    if (!built) {
      kids.forEach((c) => ul.appendChild(makeTreeLi(c)));
      built = true;
    }
    ul.style.display = "";
    tw.textContent = "▼";
  };
  const collapse = () => { ul.style.display = "none"; tw.textContent = "▶"; };
  li._expand = expand;
  li._collapse = collapse;
  li._ul = ul;
  li._isOpen = () => ul.style.display !== "none";

  tw.addEventListener("click", (e) => {
    e.stopPropagation();
    li._isOpen() ? collapse() : expand();
  });
  node.addEventListener("click", () => showPanel(name));
  node.addEventListener("dblclick", () => { state.root = name; syncRootSelect(); renderTree(); });
  return li;
}

function renderTree() {
  document.getElementById("tree").style.display = "block";
  document.getElementById("cy").style.display = "none";
  document.getElementById("deg").style.display = "none";
  const host = document.getElementById("tree");
  host.innerHTML = "";
  const ul = document.createElement("ul");
  const rootLi = makeTreeLi(state.root);
  ul.appendChild(rootLi);
  host.appendChild(ul);
  rootLi._expand(); // open first level
  host._rootLi = rootLi;
  const count = reachSize(state.root);
  document.getElementById("meta").textContent =
    `commit ${DATA.commit} · ${state.dataset} |G|=${g().size} N=${g().num} · ${count} nodes reachable (double-click to drill in)`;
}

// BFS over the dependency DAG: path of names from root to target (inclusive)
function pathTo(root, target) {
  if (root === target) return [root];
  const prev = new Map([[root, null]]);
  const q = [root];
  while (q.length) {
    const x = q.shift();
    for (const c of directRefs(x)) {
      if (!prev.has(c)) {
        prev.set(c, x);
        if (c === target) {
          const path = [];
          let cur = c;
          while (cur !== null) { path.unshift(cur); cur = prev.get(cur); }
          return path;
        }
        q.push(c);
      }
    }
  }
  return null;
}

function clearHighlight() {
  document
    .querySelectorAll("#tree .tnode.hl, #tree .tnode.target")
    .forEach((n) => n.classList.remove("hl", "target"));
}

// expand the tree along `path` and highlight it; returns the target li
function highlightPath(path) {
  clearHighlight();
  const host = document.getElementById("tree");
  let li = host._rootLi;
  if (!li || li.querySelector(".tnode").dataset.name !== path[0]) return;
  for (let i = 0; i < path.length; i++) {
    const node = li.querySelector(":scope > .tnode");
    node.classList.add(i === path.length - 1 ? "target" : "hl");
    if (i === path.length - 1) {
      node.scrollIntoView({ block: "center", behavior: "smooth" });
      showPanel(path[i]);
      break;
    }
    li._expand();
    const next = Array.from(li._ul.children).find(
      (c) => c.querySelector(":scope > .tnode").dataset.name === path[i + 1]
    );
    if (!next) break;
    li = next;
  }
}

function doSearch(name) {
  name = (name || "").trim();
  if (!name || !g().info[name]) return;
  if (state.view === "tree") {
    const path = pathTo(state.root, name);
    if (path) {
      highlightPath(path);
    } else {
      state.root = name;
      syncRootSelect();
      renderTree();
      highlightPath([name]);
    }
  } else {
    // default: highlight the name's path in the trie
    if (state.view !== "trie") setView("trie");
    highlightTriePath(name);
  }
}

// ---- name trie (compressed / radix prefix tree over theorem names) ----
const _trieCache = {};
function buildTrie(names) {
  const root = { label: "", name: null, children: new Map() };
  for (const nm of names) {
    let node = root;
    for (const ch of nm) {
      let c = node.children.get(ch);
      if (!c) { c = { label: ch, name: null, children: new Map() }; node.children.set(ch, c); }
      node = c;
    }
    node.name = nm;
  }
  // compress non-branching, non-terminal chains into single edges (radix tree)
  const compress = (node, isRoot) => {
    node.children.forEach((c) => compress(c, false));
    if (!isRoot) {
      while (node.children.size === 1 && node.name === null) {
        const c = node.children.values().next().value;
        node.label += c.label;
        node.name = c.name;
        node.children = c.children;
      }
    }
  };
  compress(root, true);
  return root;
}

function trieRoot() {
  if (!_trieCache[state.dataset]) {
    const root = buildTrie(Object.keys(g().info));
    // assign a stable id (= accumulated prefix) and subtree name-count to each node
    const finalize = (node, prefix) => {
      node.id = prefix + node.label; // root: "" + "" = ""
      let cnt = node.name ? 1 : 0;
      node.children.forEach((c) => (cnt += finalize(c, node.id)));
      node.count = cnt;
      return cnt;
    };
    finalize(root, "");
    _trieCache[state.dataset] = root;
  }
  return _trieCache[state.dataset];
}

// node ids (= prefixes) whose children are currently shown in the trie graph
let trieOpen = new Set([""]);
const RID = "·"; // display id for the empty root

function trieNodeById(id) {
  const root = trieRoot();
  if (id === "" || id === RID) return root;
  let node = root, rem = id;
  while (rem.length) {
    let f = null;
    for (const c of node.children.values()) {
      if (rem.startsWith(c.label)) { f = c; rem = rem.slice(c.label.length); break; }
    }
    if (!f) return null;
    node = f;
  }
  return node;
}

// build Cytoscape elements for the currently-expanded portion of the trie
function trieElements() {
  const root = trieRoot();
  const els = [];
  const idOf = (n) => (n.id === "" ? RID : n.id);
  const add = (node) => {
    const isTerm = !!node.name;
    const hasKids = node.children.size > 0;
    const expanded = trieOpen.has(node.id);
    let label;
    if (isTerm) label = node.name;
    else if (hasKids && !expanded) label = "+" + node.count;
    else label = "";
    els.push({
      data: {
        id: idOf(node), label,
        kind: isTerm ? nodeKind(node.name) : "node",
        term: isTerm, hasKids, expanded,
      },
    });
    if (expanded)
      node.children.forEach((c) => {
        els.push({ data: { id: "e:" + idOf(node) + ">" + idOf(c), source: idOf(node), target: idOf(c), label: c.label } });
        add(c);
      });
  };
  add(root);
  return els;
}

const trieStyle = [
  {
    selector: "node",
    style: {
      "background-color": (n) => (n.data("term") ? COLORS[n.data("kind")] || "#9aa3b5" : "#1c2230"),
      "border-width": (n) => (n.data("term") ? 2 : 1.5),
      "border-color": (n) => (n.data("hasKids") && !n.data("expanded") ? "#c9a227" : "#3a4151"),
      label: "data(label)",
      color: "#e6e9ef",
      "font-size": 11,
      "font-family": "ui-monospace, Menlo, monospace",
      "text-valign": "center",
      "text-halign": "center",
      shape: "ellipse",
      width: (n) => (n.data("term") ? Math.max(26, n.data("label").length * 7 + 10) : 22),
      height: 22,
      "text-outline-color": "#0f1115",
      "text-outline-width": 2,
    },
  },
  {
    selector: "edge",
    style: {
      width: 1.5,
      "line-color": "#46506b",
      "target-arrow-color": "#46506b",
      "target-arrow-shape": "triangle",
      "arrow-scale": 0.8,
      "curve-style": "bezier",
      label: "data(label)",
      "font-size": 11,
      "font-family": "ui-monospace, Menlo, monospace",
      color: "#cfd6e6",
      "text-background-color": "#0f1115",
      "text-background-opacity": 1,
      "text-background-padding": 1,
    },
  },
  { selector: "node:selected", style: { "border-width": 3, "border-color": "#fff" } },
  { selector: ".trie-hl", style: { "line-color": "#c9a227", "target-arrow-color": "#c9a227", width: 3 } },
  { selector: ".trie-tgt", style: { "border-width": 3, "border-color": COLORS.lemma } },
];

function renderTrie() {
  document.getElementById("tree").style.display = "none";
  document.getElementById("cy").style.display = "block";
  document.getElementById("deg").style.display = "none";
  if (cy) cy.destroy();
  cy = cytoscape({
    container: document.getElementById("cy"),
    elements: trieElements(),
    style: trieStyle,
    wheelSensitivity: 0.2,
  });
  cy.layout({ name: "dagre", rankDir: "TB", nodeSep: 16, rankSep: 44 }).run();
  cy.on("tap", "node", (evt) => {
    const d = evt.target.data();
    const node = trieNodeById(d.id);
    if (d.term && node && node.name) showPanel(node.name);
    if (d.hasKids && d.id !== RID) {
      if (trieOpen.has(node.id)) {
        // collapse this node's subtree
        trieOpen = new Set([...trieOpen].filter((x) => !(x === node.id || x.startsWith(node.id))));
      } else trieOpen.add(node.id);
      renderTrie();
    } else if (d.hasKids && d.id === RID) {
      // root toggles all top branches
      trieOpen.add("");
    }
  });
  const n = Object.keys(g().info).length;
  document.getElementById("meta").textContent =
    `commit ${DATA.commit} · ${state.dataset} · trie of ${n} names · click a node to expand`;
}

// expand the path spelling `name` and highlight it on the trie graph
function highlightTriePath(name) {
  const root = trieRoot();
  let node = root, rem = name;
  const ids = [root.id];
  while (rem.length) {
    let f = null;
    for (const c of node.children.values()) {
      if (rem.startsWith(c.label)) { f = c; rem = rem.slice(c.label.length); break; }
    }
    if (!f) return;
    node = f; ids.push(node.id);
  }
  if (node.name !== name) return;
  ids.forEach((id) => trieOpen.add(id)); // open every ancestor so the path is visible
  renderTrie();
  const idOf = (id) => (id === "" ? RID : id);
  // highlight edges + target
  for (let i = 0; i < ids.length - 1; i++) {
    const e = cy.getElementById("e:" + idOf(ids[i]) + ">" + idOf(ids[i + 1]));
    if (e) e.addClass("trie-hl");
  }
  const tgt = cy.getElementById(idOf(ids[ids.length - 1]));
  if (tgt) {
    tgt.addClass("trie-tgt");
    tgt.select();
    cy.animate({ center: { eles: tgt }, zoom: 1.2 }, { duration: 350 });
  }
  if (g().info[name]) showPanel(name);
}

function buildElements(root) {
  const { nodes, edges } = reachable(root);
  const els = [];
  nodes.forEach((name) => {
    const kind = nodeKind(name);
    els.push({
      data: { id: name, label: name, kind },
    });
  });
  edges.forEach((e, i) => {
    els.push({
      data: {
        id: "e" + i,
        source: e.p,
        target: e.q,
        label: e.count > 1 ? "x" + e.count : "",
      },
    });
  });
  return { els, count: nodes.size };
}

const baseStyle = [
  {
    selector: "node",
    style: {
      "background-color": (n) => COLORS[n.data("kind")] || "#9aa3b5",
      label: "data(label)",
      color: "#e6e9ef",
      "font-size": 10,
      "text-valign": "center",
      "text-halign": "center",
      width: 18,
      height: 18,
      "text-outline-color": "#0f1115",
      "text-outline-width": 2,
    },
  },
  {
    selector: "edge",
    style: {
      width: 1,
      "line-color": "#3a4151",
      "target-arrow-color": "#3a4151",
      "target-arrow-shape": "triangle",
      "arrow-scale": 0.7,
      "curve-style": "bezier",
      label: "data(label)",
      "font-size": 8,
      color: "#8b93a7",
    },
  },
  { selector: "node:selected", style: { "border-width": 3, "border-color": "#fff" } },
];

function renderGraph() {
  document.getElementById("tree").style.display = "none";
  document.getElementById("cy").style.display = "block";
  document.getElementById("deg").style.display = "none";
  const { els, count } = buildElements(state.root);
  if (cy) cy.destroy();
  cy = cytoscape({
    container: document.getElementById("cy"),
    elements: els,
    style: baseStyle,
    wheelSensitivity: 0.2,
  });
  if (state.view === "dag") {
    cy.layout({ name: "dagre", rankDir: "TB", nodeSep: 14, rankSep: 36 }).run();
  } else {
    // network view: size nodes by in-degree, force layout
    const indeg = {};
    cy.edges().forEach((e) => {
      indeg[e.target().id()] = (indeg[e.target().id()] || 0) + 1;
    });
    cy.nodes().forEach((n) => {
      const d = indeg[n.id()] || 0;
      const s = 14 + Math.min(40, d * 4);
      n.style({ width: s, height: s });
    });
    cy.layout({ name: "cose", animate: false, nodeRepulsion: 6000 }).run();
  }
  cy.on("tap", "node", (evt) => showPanel(evt.target.id()));
  document.getElementById("meta").textContent =
    `commit ${DATA.commit} · ${state.dataset} |G|=${g().size} N=${g().num} · ${count} nodes in this proof`;
}

function showPanel(name) {
  const info = g().info[name] || {};
  const prod = g().productions[name];
  const panel = document.getElementById("panel");
  const ess = (info.ess || [])
    .map((s, i) => `<div>${mmRender(s)}</div>`)
    .join("");
  panel.innerHTML = `
    <h2>${escapeHtml(name)}</h2>
    <div class="kind">${info.kind || "terminal"}${
    prod ? " · arity " + prod.arity : ""
  }</div>
    ${ess ? `<div class="ess"><div class="esslabel">hypotheses</div>${ess}</div>` : ""}
    <div class="stmt">${mmRender(info.statement || "")}</div>
    <div class="row"><span>in-degree (ref)</span><span>${info.ref ?? 0}</span></div>
    <div class="row"><span>save-value</span><span>${info.sav ?? 0}</span></div>
  `;
}

function escapeHtml(s) {
  return String(s).replace(/[&<>"]/g, (c) =>
    ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c])
  );
}

// ---- log-log in-degree CCDF (Fig. 1) ----
function renderDegree() {
  document.getElementById("tree").style.display = "none";
  document.getElementById("cy").style.display = "none";
  const cv = document.getElementById("deg");
  cv.style.display = "block";
  const ctx = cv.getContext("2d");
  const W = cv.width, H = cv.height, pad = 60;
  ctx.clearRect(0, 0, W, H);

  const series = [
    { name: "human", color: COLORS.thm, data: DATA.human.ccdf },
    { name: "machine", color: COLORS.lemma, data: DATA.machine.ccdf },
  ];
  // log-log domain
  let maxk = 1, mins = 1;
  series.forEach((s) =>
    s.data.forEach(([k, p]) => {
      if (k > maxk) maxk = k;
      if (p > 0 && p < mins) mins = p;
    })
  );
  const lx = (k) => pad + (Math.log10(Math.max(k, 1)) / Math.log10(maxk)) * (W - 2 * pad);
  // y-mapping: p in [mins,1] -> [top,bottom] on a log scale
  const Y = (p) => {
    const t = Math.log10(p) / Math.log10(mins); // 0 at p=1, 1 at p=mins
    return pad + t * (H - 2 * pad);
  };

  // axes
  ctx.strokeStyle = "#3a4151";
  ctx.fillStyle = "#8b93a7";
  ctx.font = "12px sans-serif";
  ctx.beginPath();
  ctx.moveTo(pad, pad);
  ctx.lineTo(pad, H - pad);
  ctx.lineTo(W - pad, H - pad);
  ctx.stroke();
  ctx.fillText("in-degree k (log)", W / 2 - 40, H - pad + 30);
  ctx.save();
  ctx.translate(pad - 38, H / 2 + 40);
  ctx.rotate(-Math.PI / 2);
  ctx.fillText("P(X ≥ k) (log)", 0, 0);
  ctx.restore();
  ctx.fillText("In-degree distribution (CCDF, log-log)", pad, pad - 20);

  series.forEach((s) => {
    ctx.strokeStyle = s.color;
    ctx.fillStyle = s.color;
    ctx.beginPath();
    let started = false;
    s.data
      .filter(([k, p]) => k >= 1 && p > 0)
      .forEach(([k, p]) => {
        const x = lx(k), y = Y(p);
        if (!started) { ctx.moveTo(x, y); started = true; } else ctx.lineTo(x, y);
      });
    ctx.stroke();
  });
  // legend
  series.forEach((s, i) => {
    ctx.fillStyle = s.color;
    ctx.fillRect(W - pad - 120, pad + i * 18, 10, 10);
    ctx.fillStyle = "#e6e9ef";
    ctx.fillText(s.name, W - pad - 104, pad + i * 18 + 9);
  });
}

// ---- controls ----
function reachSize(root) {
  return reachable(root).nodes.size;
}

function populateRoots(preferred) {
  const sel = document.getElementById("root");
  sel.innerHTML = "";
  const roots = g().roots.slice();
  // sort by transitive proof size (consistent across human/machine) so the
  // default is the same, biggest theorem in both grammars
  const sz = new Map();
  roots.forEach((r) => sz.set(r, reachSize(r)));
  roots.sort((a, b) => sz.get(b) - sz.get(a));
  roots.forEach((r) => {
    const o = document.createElement("option");
    o.value = r;
    o.textContent = `${r} (${sz.get(r)})`;
    sel.appendChild(o);
  });
  // keep the previously selected theorem if it still exists
  state.root = preferred && roots.includes(preferred) ? preferred : roots[0];
  syncRootSelect();
}

// set the dropdown to state.root, adding a one-off option if it isn't a root
function syncRootSelect() {
  const sel = document.getElementById("root");
  if (!Array.from(sel.options).some((o) => o.value === state.root)) {
    const o = document.createElement("option");
    o.value = state.root;
    o.textContent = `${state.root} (${reachSize(state.root)})`;
    sel.insertBefore(o, sel.firstChild);
  }
  sel.value = state.root;
}

function populateNames() {
  const dl = document.getElementById("names");
  dl.innerHTML = "";
  Object.keys(g().info)
    .sort()
    .forEach((n) => {
      const o = document.createElement("option");
      o.value = n;
      dl.appendChild(o);
    });
}

function setView(view) {
  state.view = view;
  document.querySelectorAll(".tabs button").forEach((x) =>
    x.classList.toggle("active", x.dataset.view === view)
  );
  refresh();
}

function refresh() {
  if (state.view === "trie") renderTrie();
  else if (state.view === "tree") renderTree();
  else if (state.view === "deg") renderDegree();
  else renderGraph();
}

function init() {
  document.getElementById("dataset").addEventListener("change", (e) => {
    const keep = state.root;
    state.dataset = e.target.value;
    trieOpen = new Set([""]);
    populateRoots(keep);
    populateNames();
    refresh();
  });
  document.getElementById("root").addEventListener("change", (e) => {
    state.root = e.target.value;
    refresh();
  });
  const search = document.getElementById("search");
  search.addEventListener("keydown", (e) => {
    if (e.key === "Enter") { e.preventDefault(); doSearch(search.value); }
  });
  search.addEventListener("change", () => doSearch(search.value));
  const showstmt = document.getElementById("showstmt");
  const applyStmt = () => document.body.classList.toggle("nostmt", !showstmt.checked);
  showstmt.addEventListener("change", applyStmt);
  applyStmt();
  document.querySelectorAll(".tabs button").forEach((b) => {
    b.addEventListener("click", () => setView(b.dataset.view));
  });
  populateRoots();
  populateNames();
  refresh();
}

fetch("data/data.json")
  .then((r) => {
    if (!r.ok) throw new Error("data.json not found");
    return r.json();
  })
  .then((d) => {
    DATA = d;
    init();
  })
  .catch((err) => {
    document.getElementById("cy").innerHTML =
      `<div style="padding:40px;color:#8b93a7">Could not load data/data.json.<br>` +
      `Run <code>dune exec bin/main.exe -- export 1000</code> then serve this folder:<br>` +
      `<code>cd visualization &amp;&amp; python3 -m http.server</code><br><br>${err}</div>`;
  });
