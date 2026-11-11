(() => {
  "use strict";

  const palette = ["#c85b54", "#4298c1", "#e89a22", "#9467a8", "#506e8d", "#279782"];
  const canvas = document.getElementById("map");
  const ctx = canvas.getContext("2d");
  const state = {
    features: [],
    nodes: [],
    edges: [],
    adjacency: [],
    nodeByCoordinate: new Map(),
    tree: [],
    branchStats: [],
    branches: 0,
    destination: -1,
    scale: 1,
    offsetX: 0,
    offsetY: 0,
    dragging: false,
    moved: false
  };
  const bounds = { minX: 34.2704, maxX: 35.8543, minY: 29.4923, maxY: 33.3269 };
  let frame = 0;

  class MinHeap {
    constructor() { this.items = []; }

    push(node, distance) {
      const item = { node, distance };
      let index = this.items.length;
      this.items.push(item);
      while (index > 0) {
        const parent = (index - 1) >> 1;
        if (this.items[parent].distance <= distance) break;
        this.items[index] = this.items[parent];
        index = parent;
      }
      this.items[index] = item;
    }

    pop() {
      if (this.items.length === 0) return null;
      const first = this.items[0];
      const last = this.items.pop();
      if (this.items.length > 0 && last) {
        let index = 0;
        while (true) {
          const left = index * 2 + 1;
          const right = left + 1;
          if (left >= this.items.length) break;
          const child = right < this.items.length && this.items[right].distance < this.items[left].distance ? right : left;
          if (this.items[child].distance >= last.distance) break;
          this.items[index] = this.items[child];
          index = child;
        }
        this.items[index] = last;
      }
      return first;
    }
  }

  function coordinateKey(point) {
    return `${Math.round(point[0] * 100000)},${Math.round(point[1] * 100000)}`;
  }

  function nodeFor(point, indexByCoordinate = state.nodeByCoordinate) {
    const key = coordinateKey(point);
    const existing = indexByCoordinate.get(key);
    if (existing !== undefined) return existing;
    const index = state.nodes.length;
    state.nodes.push({ lon: point[0], lat: point[1] });
    state.adjacency.push([]);
    indexByCoordinate.set(key, index);
    return index;
  }

  function lineLength(line) {
    let length = 0;
    for (let i = 1; i < line.length; i++) {
      const a = line[i - 1], b = line[i];
      const middleLatitude = (a[1] + b[1]) * Math.PI / 360;
      const dx = (b[0] - a[0]) * Math.cos(middleLatitude) * 111320;
      const dy = (b[1] - a[1]) * 110574;
      length += Math.hypot(dx, dy);
    }
    return length;
  }

  function addGraphEdge(a, b, featureIndex, geometry) {
    if (a === b) return -1;
    const length = lineLength(geometry);
    if (!Number.isFinite(length) || length <= 0) return -1;
    const edgeIndex = state.edges.length;
    state.edges.push({ a, b, featureIndex, geometry, length, active: true });
    state.adjacency[a].push(edgeIndex);
    state.adjacency[b].push(edgeIndex);
    return edgeIndex;
  }

  function buildGraph(features) {
    state.features = features;
    state.nodes = [];
    state.edges = [];
    state.adjacency = [];
    state.nodeByCoordinate = new Map();

    features.forEach((feature, featureIndex) => {
      const lines = feature.geometry.type === "LineString"
        ? [feature.geometry.coordinates]
        : feature.geometry.coordinates;
      for (const line of lines) {
        if (line.length < 2) continue;
        const a = nodeFor(line[0]);
        const b = nodeFor(line[line.length - 1]);
        addGraphEdge(a, b, featureIndex, line);
      }
    });
  }

  function nearestRoadPosition(lon, lat) {
    const longitudeScale = Math.cos(lat * Math.PI / 180) * 111320;
    const latitudeScale = 110574;
    let best = null;
    let bestDistance = Infinity;
    for (let edgeIndex = 0; edgeIndex < state.edges.length; edgeIndex++) {
      const edge = state.edges[edgeIndex];
      if (!edge.active) continue;
      const line = edge.geometry;
      for (let segmentIndex = 0; segmentIndex < line.length - 1; segmentIndex++) {
        const a = line[segmentIndex], b = line[segmentIndex + 1];
        const ax = (a[0] - lon) * longitudeScale, ay = (a[1] - lat) * latitudeScale;
        const bx = (b[0] - lon) * longitudeScale, by = (b[1] - lat) * latitudeScale;
        const dx = bx - ax, dy = by - ay;
        const denominator = dx * dx + dy * dy;
        const t = denominator === 0 ? 0 : Math.max(0, Math.min(1, -(ax * dx + ay * dy) / denominator));
        const distance = Math.hypot(ax + t * dx, ay + t * dy);
        if (distance < bestDistance) {
          bestDistance = distance;
          best = {
            edgeIndex,
            segmentIndex,
            t,
            point: [a[0] + t * (b[0] - a[0]), a[1] + t * (b[1] - a[1])]
          };
        }
      }
    }
    return best ? { ...best, distance: bestDistance } : null;
  }

  function splitEdgeAt(position) {
    const edge = state.edges[position.edgeIndex];
    const line = edge.geometry;
    const atStart = position.segmentIndex === 0 && position.t < 0.00001;
    const atEnd = position.segmentIndex === line.length - 2 && position.t > 0.99999;
    if (atStart) return edge.a;
    if (atEnd) return edge.b;

    const pointKey = coordinateKey(position.point);
    const existing = state.nodeByCoordinate.get(pointKey);
    if (existing !== undefined) return existing;

    const node = nodeFor(position.point);
    edge.active = false;
    state.adjacency[edge.a] = state.adjacency[edge.a].filter(index => index !== position.edgeIndex);
    state.adjacency[edge.b] = state.adjacency[edge.b].filter(index => index !== position.edgeIndex);
    const splitPoint = [position.point[0], position.point[1]];
    const first = line.slice(0, position.segmentIndex + 1).concat([splitPoint]);
    const second = [splitPoint].concat(line.slice(position.segmentIndex + 1));
    addGraphEdge(edge.a, node, edge.featureIndex, first);
    addGraphEdge(node, edge.b, edge.featureIndex, second);
    return node;
  }

  function calculateTree(root) {
    const count = state.nodes.length;
    const distances = new Float64Array(count);
    distances.fill(Infinity);
    const parents = new Int32Array(count);
    parents.fill(-1);
    const parentEdges = new Int32Array(count);
    parentEdges.fill(-1);
    const visited = new Uint8Array(count);
    const order = [];
    const heap = new MinHeap();
    distances[root] = 0;
    heap.push(root, 0);

    while (heap.items.length > 0) {
      const current = heap.pop();
      if (!current || visited[current.node] || current.distance !== distances[current.node]) continue;
      visited[current.node] = 1;
      order.push(current.node);

      for (const edgeIndex of state.adjacency[current.node]) {
        const edge = state.edges[edgeIndex];
        const neighbor = edge.a === current.node ? edge.b : edge.a;
        const distance = current.distance + edge.length;
        if (distance < distances[neighbor]) {
          distances[neighbor] = distance;
          parents[neighbor] = current.node;
          parentEdges[neighbor] = edgeIndex;
          heap.push(neighbor, distance);
        }
      }
    }

    const children = order.filter(node => parents[node] === root);
    const origin = state.nodes[root];
    children.sort((a, b) => {
      const angleA = Math.atan2(state.nodes[a].lat - origin.lat, (state.nodes[a].lon - origin.lon) * Math.cos(origin.lat * Math.PI / 180));
      const angleB = Math.atan2(state.nodes[b].lat - origin.lat, (state.nodes[b].lon - origin.lon) * Math.cos(origin.lat * Math.PI / 180));
      return angleA - angleB;
    });

    const subtreeSize = new Uint32Array(count);
    subtreeSize.fill(1);
    for (let i = order.length - 1; i > 0; i--) {
      const node = order[i];
      subtreeSize[parents[node]] += subtreeSize[node];
    }

    const childrenByParent = Array.from({ length: count }, () => []);
    for (let i = 1; i < order.length; i++) childrenByParent[parents[order[i]]].push(order[i]);
    const branchForNode = new Uint8Array(count);
    branchForNode.fill(255);
    const rootSeeds = children.slice().sort((a, b) => subtreeSize[b] - subtreeSize[a]).slice(0, 1);
    const branchRoots = rootSeeds.slice();
    const isAncestor = (ancestor, node) => {
      for (let current = node; current >= 0; current = parents[current]) {
        if (current === ancestor) return true;
      }
      return false;
    };

    const assignBranches = () => {
      branchForNode.fill(255);
      const branchIndex = new Map(branchRoots.map((node, index) => [node, index]));
      const rootAngles = rootSeeds.map(node => {
        const point = state.nodes[node];
        return Math.atan2(point.lat - origin.lat, (point.lon - origin.lon) * Math.cos(origin.lat * Math.PI / 180));
      });

      for (const node of order) {
        if (node === root) continue;
        const directBranch = branchIndex.get(node);
        if (directBranch !== undefined) {
          branchForNode[node] = directBranch;
        } else if (parents[node] === root) {
          const point = state.nodes[node];
          const angle = Math.atan2(point.lat - origin.lat, (point.lon - origin.lon) * Math.cos(origin.lat * Math.PI / 180));
          let nearestBranch = 0;
          let smallestAngle = Infinity;
          for (let i = 0; i < rootAngles.length; i++) {
            const difference = Math.abs(Math.atan2(Math.sin(angle - rootAngles[i]), Math.cos(angle - rootAngles[i])));
            if (difference < smallestAngle) {
              smallestAngle = difference;
              nearestBranch = i;
            }
          }
          branchForNode[node] = nearestBranch;
        } else {
          branchForNode[node] = branchForNode[parents[node]];
        }
      }
      return branchForNode;
    };

    while (branchRoots.length < palette.length) {
      assignBranches();
      const branchCounts = new Uint32Array(palette.length);
      for (const node of order) {
        if (node !== root) branchCounts[branchForNode[node]]++;
      }
      const branchOrder = Array.from({ length: palette.length }, (_, index) => index)
        .sort((a, b) => branchCounts[b] - branchCounts[a]);
      let largestBranch = -1;
      let candidates = [];
      for (const branch of branchOrder) {
        const branchCandidates = [];
        for (const node of order) {
          if (node !== root && branchForNode[node] !== branch) continue;
          for (const child of childrenByParent[node]) {
            if (branchForNode[child] !== branch) continue;
            if (branchRoots.some(branchRoot => isAncestor(child, branchRoot))) continue;
            branchCandidates.push({ node: child, fork: childrenByParent[node].length > 1, size: subtreeSize[child] });
          }
        }
        if (branchCandidates.length > 0) {
          largestBranch = branch;
          candidates = branchCandidates;
          break;
        }
      }
      if (candidates.length === 0) break;
      const targetSize = branchCounts[largestBranch] / 2;
      candidates.sort((a, b) => {
        const scoreA = Math.abs(a.size - targetSize) + (a.fork ? 0 : targetSize * 0.12);
        const scoreB = Math.abs(b.size - targetSize) + (b.fork ? 0 : targetSize * 0.12);
        return scoreA - scoreB;
      });
      branchRoots.push(candidates[0].node);
    }
    assignBranches();

    const branchNodeCounts = new Uint32Array(palette.length);
    for (const node of order) {
      if (node !== root) branchNodeCounts[branchForNode[node]]++;
    }

    state.destination = root;
    state.branches = branchRoots.length;
    if (state.branches !== palette.length) {
      throw new Error(`לא ניתן לפצל את הרשת לשישה ענפים: נמצאו ${state.branches} בלבד.`);
    }
    state.branchStats = branchRoots.map((node, index) => {
      const point = state.nodes[node];
      const angle = Math.atan2(point.lat - origin.lat, (point.lon - origin.lon) * Math.cos(origin.lat * Math.PI / 180));
      const directions = ["מזרחה", "צפון־מזרחה", "צפונה", "צפון־מערבה", "מערבה", "דרום־מערבה", "דרומה", "דרום־מזרחה"];
      const directionIndex = (Math.round(angle / (Math.PI / 4)) + 8) % 8;
      return {
        index,
        direction: directions[directionIndex],
        share: branchNodeCounts[index] / Math.max(1, order.length - 1)
      };
    });
    state.tree = order.slice(1).map(node => ({
      edgeIndex: parentEdges[node],
      branch: branchForNode[node],
      size: subtreeSize[node]
    })).sort((a, b) => a.size - b.size);
    updateSummary(order.length);
    requestDraw();
  }

  function updateSummary(connectedNodes) {
    document.getElementById("stat-segments").textContent = state.tree.length.toLocaleString("he-IL");
    document.getElementById("stat-junctions").textContent = connectedNodes.toLocaleString("he-IL");
    const point = state.nodes[state.destination];
    document.getElementById("destination-coordinate").textContent = `${point.lat.toFixed(4)}, ${point.lon.toFixed(4)}`;
    document.getElementById("status").textContent =
      `יעד ${point.lat.toFixed(3)}, ${point.lon.toFixed(3)} · ${state.branches} ענפים`;
    const legend = document.getElementById("branch-legend");
    legend.replaceChildren();
    for (const branch of state.branchStats) {
      const item = document.createElement("li");
      const line = document.createElement("span");
      line.className = "branch-line";
      line.style.backgroundColor = palette[branch.index];
      const label = document.createElement("span");
      label.textContent = `ענף ${branch.index + 1} · ${Math.round(branch.share * 100)}% · ${branch.direction}`;
      item.append(line, label);
      legend.append(item);
    }
  }

  function projectionParameters(width, height) {
    const latitudeScale = Math.cos(31.3 * Math.PI / 180);
    const minX = bounds.minX * latitudeScale, maxX = bounds.maxX * latitudeScale;
    const padding = Math.max(34, Math.min(width, height) * 0.075);
    const fit = Math.min(
      (width - padding * 2) / (maxX - minX),
      (height - padding * 2) / (bounds.maxY - bounds.minY)
    );
    return { latitudeScale, minX, maxX, fit };
  }

  function project(point, width, height, interactive = true) {
    const { latitudeScale, minX, maxX, fit } = projectionParameters(width, height);
    const scale = interactive ? state.scale : 1;
    const offsetX = interactive ? state.offsetX : 0;
    const offsetY = interactive ? state.offsetY : 0;
    return {
      x: width / 2 + (point[0] * latitudeScale - (minX + maxX) / 2) * fit * scale + offsetX,
      y: height / 2 - (point[1] - (bounds.minY + bounds.maxY) / 2) * fit * scale + offsetY
    };
  }

  function unproject(x, y, width, height) {
    const { latitudeScale, minX, maxX, fit } = projectionParameters(width, height);
    const mapX = (x - width / 2 - state.offsetX) / (fit * state.scale) + (minX + maxX) / 2;
    const latitude = (bounds.minY + bounds.maxY) / 2 - (y - height / 2 - state.offsetY) / (fit * state.scale);
    return { lon: mapX / latitudeScale, lat: latitude };
  }

  function appendLine(line, width, height) {
    if (line.length < 2) return;
    const first = project(line[0], width, height);
    ctx.moveTo(first.x, first.y);
    for (let i = 1; i < line.length; i++) {
      const point = project(line[i], width, height);
      ctx.lineTo(point.x, point.y);
    }
  }

  function requestDraw() {
    if (frame) return;
    frame = requestAnimationFrame(() => { frame = 0; draw(); });
  }

  function draw() {
    const rect = canvas.getBoundingClientRect();
    const dpr = Math.min(window.devicePixelRatio || 1, 2);
    const width = Math.max(1, rect.width), height = Math.max(1, rect.height);
    if (canvas.width !== Math.round(width * dpr) || canvas.height !== Math.round(height * dpr)) {
      canvas.width = Math.round(width * dpr);
      canvas.height = Math.round(height * dpr);
    }
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, width, height);
    ctx.fillStyle = "#fbfaf6";
    ctx.fillRect(0, 0, width, height);
    drawGrid(width, height);

    if (state.features.length > 0) {
      ctx.beginPath();
      for (const feature of state.features) {
        const lines = feature.geometry.type === "LineString" ? [feature.geometry.coordinates] : feature.geometry.coordinates;
        for (const line of lines) appendLine(line, width, height);
      }
      ctx.strokeStyle = "#deded9";
      ctx.lineWidth = 0.55;
      ctx.stroke();
    }

    ctx.lineCap = "round";
    ctx.lineJoin = "round";
    for (const item of state.tree) {
      const edge = state.edges[item.edgeIndex];
      const lineWidth = 0.3 + Math.sqrt(item.size / Math.max(1, state.tree.length)) * 4.8;
      ctx.beginPath();
      appendLine(edge.geometry, width, height);
      ctx.strokeStyle = palette[item.branch % palette.length];
      ctx.lineWidth = lineWidth;
      ctx.stroke();
    }

    if (state.destination >= 0) drawDestination(width, height);
  }

  function drawGrid(width, height) {
    const step = 38;
    ctx.save();
    ctx.strokeStyle = "rgba(128, 128, 120, .025)";
    ctx.lineWidth = 1;
    ctx.beginPath();
    for (let x = (state.offsetX % step + step) % step; x < width; x += step) {
      ctx.moveTo(x, 0); ctx.lineTo(x, height);
    }
    for (let y = (state.offsetY % step + step) % step; y < height; y += step) {
      ctx.moveTo(0, y); ctx.lineTo(width, y);
    }
    ctx.stroke();
    ctx.restore();
  }

  function drawDestination(width, height) {
    const node = state.nodes[state.destination];
    const point = project([node.lon, node.lat], width, height);
    ctx.save();
    ctx.beginPath();
    ctx.arc(point.x, point.y, 13, 0, Math.PI * 2);
    ctx.fillStyle = "rgba(50, 59, 64, .12)";
    ctx.fill();
    ctx.beginPath();
    ctx.arc(point.x, point.y, 5, 0, Math.PI * 2);
    ctx.fillStyle = "#fbfaf6";
    ctx.fill();
    ctx.strokeStyle = "#343a3d";
    ctx.lineWidth = 2.3;
    ctx.stroke();
    ctx.beginPath();
    ctx.arc(point.x, point.y, 2, 0, Math.PI * 2);
    ctx.fillStyle = "#4298c1";
    ctx.fill();
    ctx.restore();
  }

  function chooseDestination(x, y) {
    const point = unproject(x, y, canvas.clientWidth, canvas.clientHeight);
    const nearest = nearestRoadPosition(point.lon, point.lat);
    if (nearest) calculateTree(splitEdgeAt(nearest));
  }

  function zoom(factor) {
    const previous = state.scale;
    state.scale = Math.min(12, Math.max(1, state.scale * factor));
    const applied = state.scale / previous;
    state.offsetX *= applied;
    state.offsetY *= applied;
    requestDraw();
  }

  function escapeXml(value) {
    return value.replace(/[<>&"']/g, char => ({ "<": "&lt;", ">": "&gt;", "&": "&amp;", '"': "&quot;", "'": "&apos;" })[char]);
  }

  function makePosterSvg() {
    const width = 1800, height = 1060, mapWidth = 1420, mapHeight = 790;
    const mapOffsetX = 190, mapOffsetY = 130;
    const horizontalStretch = 1.6;
    const posterPoint = coordinates => {
      const point = project(coordinates, mapWidth, mapHeight, false);
      return {
        x: mapOffsetX + mapWidth / 2 + (point.x - mapWidth / 2) * horizontalStretch,
        y: mapOffsetY + point.y
      };
    };
    const paths = [];
    for (const item of state.tree) {
      const edge = state.edges[item.edgeIndex];
      const strokeWidth = (0.28 + Math.sqrt(item.size / Math.max(1, state.tree.length)) * 5).toFixed(2);
      let path = "";
      for (let i = 0; i < edge.geometry.length; i++) {
        const point = posterPoint(edge.geometry[i]);
        path += `${i ? "L" : "M"}${point.x.toFixed(1)} ${point.y.toFixed(1)} `;
      }
      if (path) {
        paths.push(`<path d="${path.trim()}" fill="none" stroke="${palette[item.branch % palette.length]}" stroke-width="${strokeWidth}" stroke-linecap="round" stroke-linejoin="round" opacity=".92"/>`);
      }
    }

    const target = state.nodes[state.destination];
    const marker = posterPoint([target.lon, target.lat]);
    const legend = state.branchStats.map(branch => {
      const x = 26 + branch.index * 288;
      const percentage = Math.round(branch.share * 100);
      return `<path d="M${x} 1008h27" stroke="${palette[branch.index]}" stroke-width="5" stroke-linecap="round"/><text x="${x + 38}" y="1014" fill="#353a3c" font-family="Arial,sans-serif" font-size="17" font-weight="700">ענף ${branch.index + 1}</text><text x="${x + 104}" y="1014" fill="#787d7e" font-family="Arial,sans-serif" font-size="14">${percentage}% · ${branch.direction}</text>`;
    }).join("");
    const title = "כל הדרכים מובילות אל היעד";
    const subtitle = `נקודת יעד ${target.lat.toFixed(4)}, ${target.lon.toFixed(4)} · מסלולים לפי מרחק גאוגרפי`;
    return `<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}" viewBox="0 0 ${width} ${height}"><rect width="100%" height="100%" fill="#fbfaf6"/><path d="M26 978H1774" stroke="#e5e3dd" stroke-width="1.5"/>${paths.join("")}<circle cx="${marker.x.toFixed(1)}" cy="${marker.y.toFixed(1)}" r="9" fill="#41484b"/><circle cx="${marker.x.toFixed(1)}" cy="${marker.y.toFixed(1)}" r="5.5" fill="#fbfaf6"/><circle cx="${marker.x.toFixed(1)}" cy="${marker.y.toFixed(1)}" r="2.3" fill="#4298c1"/><text x="26" y="42" fill="#45494a" font-family="Arial,sans-serif" font-size="21">${escapeXml(subtitle)}</text><text x="26" y="100" fill="#262a2b" font-family="Arial,sans-serif" font-size="57" font-weight="750">${escapeXml(title)}</text><text x="1774" y="38" text-anchor="end" fill="#868888" font-family="Arial,sans-serif" font-size="14">ישראל · שכבת הדרכים הארצית של משרד התחבורה</text><text x="1774" y="61" text-anchor="end" fill="#868888" font-family="Arial,sans-serif" font-size="14">עובי הקו ∝ מספר הצמתים שממשיכים בכל ענף</text><text x="1774" y="84" text-anchor="end" fill="#383c3d" font-family="Arial,sans-serif" font-size="15" font-weight="700">6 ענפים צבעוניים · ללא זמני נסיעה</text>${legend}<text x="1774" y="1040" text-anchor="end" fill="#777c7d" font-family="Arial,sans-serif" font-size="12">משרד התחבורה · מספרי דרכים ארציות · רישיון CC BY</text></svg>`;
  }

  function downloadBlob(blob, filename) {
    const link = document.createElement("a");
    const url = URL.createObjectURL(blob);
    link.href = url;
    link.download = filename;
    link.click();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  }

  function exportSvg() {
    downloadBlob(new Blob([makePosterSvg()], { type: "image/svg+xml;charset=utf-8" }), "israel-roads-to-destination.svg");
  }

  async function exportPng() {
    const svgUrl = URL.createObjectURL(new Blob([makePosterSvg()], { type: "image/svg+xml;charset=utf-8" }));
    try {
      const image = new Image();
      image.src = svgUrl;
      await image.decode();
      const poster = document.createElement("canvas");
      poster.width = 3600;
      poster.height = 2120;
      const posterContext = poster.getContext("2d");
      if (!posterContext) throw new Error("לא ניתן ליצור משטח לציור הפוסטר.");
      posterContext.drawImage(image, 0, 0, poster.width, poster.height);
      const blob = await new Promise((resolve, reject) => {
        poster.toBlob(result => result ? resolve(result) : reject(new Error("יצירת קובץ PNG נכשלה.")), "image/png");
      });
      downloadBlob(blob, "israel-roads-to-destination.png");
    } catch (error) {
      const errorBox = document.getElementById("error");
      errorBox.textContent = `ייצוא הפוסטר נכשל: ${error.message}`;
      errorBox.classList.remove("hidden");
      console.error("Could not export poster PNG:", error);
    } finally {
      URL.revokeObjectURL(svgUrl);
    }
  }

  function bindEvents() {
    document.getElementById("zoom-in").addEventListener("click", () => zoom(1.35));
    document.getElementById("zoom-out").addEventListener("click", () => zoom(1 / 1.35));
    document.getElementById("zoom-reset").addEventListener("click", () => {
      state.scale = 1;
      state.offsetX = 0;
      state.offsetY = 0;
      requestDraw();
    });
    document.getElementById("download-png").addEventListener("click", async event => {
      const button = event.currentTarget;
      button.disabled = true;
      try {
        await exportPng();
      } finally {
        button.disabled = false;
      }
    });
    document.getElementById("download-svg").addEventListener("click", exportSvg);
    canvas.addEventListener("pointerdown", event => {
      state.dragging = true;
      state.moved = false;
      state.startX = event.clientX;
      state.startY = event.clientY;
      state.lastX = event.clientX;
      state.lastY = event.clientY;
      canvas.setPointerCapture(event.pointerId);
    });
    canvas.addEventListener("pointermove", event => {
      if (!state.dragging) return;
      const dx = event.clientX - state.lastX, dy = event.clientY - state.lastY;
      if (Math.hypot(event.clientX - state.startX, event.clientY - state.startY) > 4) state.moved = true;
      state.offsetX += dx;
      state.offsetY += dy;
      state.lastX = event.clientX;
      state.lastY = event.clientY;
      requestDraw();
    });
    canvas.addEventListener("pointerup", event => {
      if (!state.moved) {
        const rect = canvas.getBoundingClientRect();
        chooseDestination(event.clientX - rect.left, event.clientY - rect.top);
      }
      state.dragging = false;
    });
    canvas.addEventListener("pointercancel", () => { state.dragging = false; });
    canvas.addEventListener("wheel", event => {
      event.preventDefault();
      zoom(event.deltaY < 0 ? 1.12 : 1 / 1.12);
    }, { passive: false });
    window.addEventListener("resize", requestDraw);
  }

  async function loadData() {
    try {
      const response = await fetch("data/roadnetwork.geojson");
      if (!response.ok) throw new Error(`שרת הנתונים החזיר ${response.status}`);
      const geojson = await response.json();
      if (!Array.isArray(geojson.features) || geojson.features.length === 0) {
        throw new Error("קובץ הנתונים לא מכיל מקטעי דרך.");
      }
      buildGraph(geojson.features);
      if (state.nodes.length === 0 || state.edges.length === 0) throw new Error("לא נמצאו צמתים וקישורים ליצירת רשת.");
      document.getElementById("download-png").disabled = false;
      document.getElementById("download-svg").disabled = false;
      const initial = nearestRoadPosition(34.78, 32.08);
      if (!initial) throw new Error("לא נמצאו מקטעי דרך לבחירת יעד.");
      calculateTree(splitEdgeAt(initial));
    } catch (error) {
      const message = location.protocol === "file:"
        ? "כדי לטעון את שכבת הדרכים יש להפעיל שרת מקומי בתיקיית הפרויקט: python -m http.server 8000, ואז לפתוח http://localhost:8000."
        : `טעינת רשת הדרכים נכשלה: ${error.message}`;
      const errorBox = document.getElementById("error");
      errorBox.textContent = message;
      errorBox.classList.remove("hidden");
      document.getElementById("status").textContent = "טעינת הרשת נכשלה";
      console.error("Could not load and build the road graph:", error);
    }
  }

  bindEvents();
  loadData();
})();
