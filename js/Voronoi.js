
var Voronoi = Voronoi || {};

(function(Voronoi) {

	// requestAnimationFrame shim
	var i = 0,
		lastTime = 0,
		vendors = ['ms', 'moz', 'webkit', 'o'];

	while (i < vendors.length && !window.requestAnimationFrame) {
		window.requestAnimationFrame = window[vendors[i] + 'RequestAnimationFrame'];
		window.cancelAnimationFrame = window[vendors[i] + 'CancelAnimationFrame'] || window[vendors[i] + 'CancelRequestAnimationFrame'];
		i++;
	}

	if (!window.requestAnimationFrame) {
		window.requestAnimationFrame = function(callback, element) {
			var currTime = new Date().getTime(),
				timeToCall = Math.max(0, 1000 / 60 - currTime + lastTime),
				id = setTimeout(function() { callback(currTime + timeToCall); }, timeToCall);

			lastTime = currTime + timeToCall;
			return id;
		};
	}

	if (!window.cancelAnimationFrame) {
		window.cancelAnimationFrame = function(id) {
			clearTimeout(id);
		};
	}

	Array.prototype.each = function(f) {
		var i = this.length;
		while (i--) {
			f(this[i]);
		}
	};

	function Edge() {
		this.data;
		this.next;
		this.rot;
	}

	Edge.prototype.splice = function(e) {
		var e1 = this.next.rot,
			e2 = e.next.rot,
			e3 = this.next;

		this.next = e.next;
		e.next = e3;

		e3 = e1.next;
		e1.next = e2.next;
		e2.next = e3;
	};

	Edge.prototype.swap = function() {
		var e0 = this.oPrev(),
			e1 = this.sym().oPrev();

		this.splice(e0);
		this.sym().splice(e1);
		this.splice(e0.lNext());
		this.sym().splice(e1.lNext());
		this.setOrg(e0.dest());
		this.setDest(e1.dest());
	};

	Edge.prototype.sym = function() {
		return this.rot.rot;
	};

	Edge.prototype.iRot = function() {
		return this.rot.rot.rot;
	};

	Edge.prototype.org = function(v) {
		return this.data;
	};

	Edge.prototype.setOrg = function(v) {
		this.data = v;
	};

	Edge.prototype.dest = function() {
		return this.rot.rot.data;
	};

	Edge.prototype.setDest = function(v) {
		this.rot.rot.data = v;
	};

	Edge.prototype.setOrgDest = function(o, d) {
		this.setOrg(o);
		this.setDest(d);
	};

	Edge.prototype.left = function() {
		return this.rot.rot.rot.data;
	};

	Edge.prototype.setLeft = function(v) {
		this.rot.rot.rot.data = v;
	};

	Edge.prototype.right = function() {
		return this.rot.data;
	};

	Edge.prototype.setRight = function(v) {
		this.rot.data = v;
	};

	Edge.prototype.oNext = function() {
		return this.next;
	};

	Edge.prototype.rNext = function() {
		return this.rot.next.rot.rot.rot;
	};

	Edge.prototype.dNext = function() {
		return this.rot.rot.next.rot.rot;
	};

	Edge.prototype.lNext = function() {
		return this.rot.rot.rot.next.rot;
	};

	Edge.prototype.oPrev = function() {
		return this.rot.next.rot;
	};

	Edge.prototype.rPrev = function() {
		return this.rot.rot.next;
	};

	Edge.prototype.dPrev = function() {
		return this.rot.rot.rot.next.rot.rot.rot;
	};

	Edge.prototype.lPrev = function() {
		return this.next.rot.rot;
	};

	Edge.prototype.leftVertex = function(v) {
		return isLeftOf(v, this.org(), this.dest());
	};

	Edge.prototype.rightVertex = function(v) {
		return isRightOf(v, this.org(), this.dest());
	};

	Edge.prototype.colinearVertex = function(v) {
		return colinear(v, this.org(), this.dest());
	};


	function Vertex(x, y) {
		this.x = x;
		this.y = y;
		this.vx = 0;
		this.vy = 0;
		this.cell = 0;
		this.isInfinity = false;
	}

	Vertex.prototype.equals = function(v) {
		return this.x === v.x && this.y === v.y;
	};


	var context,
		viewHomeDiv,
		viewOuterDiv,
		boundary = 25,
		canvasWidth,
		canvasHeight,
		totalVertices = 50,
		maxSpeed = 3,
		vertices = [],
		r,
		g,
		b,
		ri,
		gi,
		bi,
		loopID = 0,
		rot_map = [1, 2, 3, 0],
		next_map = [0, 3, 2, 1],
		edge,
		edges = [],
		circumcenters = [],
		edgeVertices = [new Vertex(0, -5000), new Vertex(-10000, 5000), new Vertex(10000, 5000)],
		maxIterations = 200;


	function inCircle(v0, v1, v2, v3) {
		var circle_test = (v2.x - v1.x) * (v3.y - v1.y) * (v0.x * v0.x + v0.y * v0.y - v1.x * v1.x - v1.y * v1.y)
			+ (v3.x - v1.x) * (v0.y - v1.y) * (v2.x * v2.x + v2.y * v2.y - v1.x * v1.x - v1.y * v1.y)
			+ (v0.x - v1.x) * (v2.y - v1.y) * (v3.x * v3.x + v3.y * v3.y - v1.x * v1.x - v1.y * v1.y)
			- (v2.x - v1.x) * (v0.y - v1.y) * (v3.x * v3.x + v3.y * v3.y - v1.x * v1.x - v1.y * v1.y)
			- (v3.x - v1.x) * (v2.y - v1.y) * (v0.x * v0.x + v0.y * v0.y - v1.x * v1.x - v1.y * v1.y)
			- (v0.x - v1.x) * (v3.y - v1.y) * (v2.x * v2.x + v2.y * v2.y - v1.x * v1.x - v1.y * v1.y);

		return circle_test >= 0;
	}

	function area(v0, v1, v2) {
		return (v1.x - v0.x) * (v2.y - v0.y) - (v2.x - v0.x) * (v1.y - v0.y);
	}

	function distSq(v0, v1) {
		return (v1.x - v0.x) * (v1.x - v0.x) + (v1.y - v0.y) * (v1.y - v0.y);
	}

	function colinear(v0, v1, v2) {
		return area(v1, v0, v2) === 0;
	}

	function isRightOf(v0, v1, v2) {
		return area(v0, v1, v2) > 0;
	}

	function isLeftOf(v0, v1, v2) {
		return area(v0, v1, v2) < 0;
	}

	function getQuadEdge() {
		var e = [new Edge(), new Edge(), new Edge(), new Edge()],
			i;

		for (i = 0; i < 4; i++) {
			e[i].rot = e[rot_map[i]];
			e[i].next = e[next_map[i]];
		}

		return e[0];
	}

	function deleteQuadEdge(e) {
		disconnect(e);
		[e, e.rot, e.sym(), e.iRot()].each(function(q) {
			delete q;
		});
	}

	function initDelaunay() {
		edges.each(function(e) {
			deleteQuadEdge(e);
		});
		edges = [];
		circumcenters = [];

		edgeVertices.each(function(v) {
			v.isInfinity = true;
		});

		edges[0] = getQuadEdge();
		edges[2] = getQuadEdge();
		edges[0].setOrgDest(edgeVertices[1], edgeVertices[2]);
		edges[2].setOrgDest(edgeVertices[1], edgeVertices[0]);
		edges[0].splice(edges[2]);
		edges[2] = edges[2].sym();
		edges[1] = connect(edges[0], edges[2]);
		edge = edges[0];
	}

	function inCosmic(v) {
		var cosmic = true;
		[edges[0], edges[1], edges[2]].each(function(e) {
			cosmic &= e.leftVertex(v);
		});
		return cosmic;
	}

	function locate(v) {
		if (edge.rightVertex(v)) {
			edge = edge.sym();
		}

		var i = 0;
		while (i++ < maxIterations && !v.equals(edge.org()) && !v.equals(edge.dest())) {
			if (!edge.oNext().rightVertex(v)) {
				edge = edge.oNext();
			} else if (!edge.dPrev().rightVertex(v)) {
				edge = edge.dPrev();
			} else {
				return edge;
			}
		}
	}

	function connect(e0, e1) {
		var e2 = getQuadEdge();
		e2.setOrgDest(e0.dest(), e1.org());
		e2.splice(e0.lNext());
		e2.sym().splice(e1);
		return e2;
	}

	function disconnect(e) {
		e.splice(e.oPrev());
		e.sym().splice(e.sym().oPrev());
	}

	function circumcenter(v0, v1, v2) {
		var denominator = (v1.y - v2.y) * (v1.x - v0.x) - (v1.y - v0.y) * (v1.x - v2.x),
			num0 = ((v0.x + v1.x) * (v1.x - v0.x)) / 2 + ((v1.y - v0.y) * (v0.y + v1.y)) / 2,
			num1 = ((v1.x + v2.x) * (v1.x - v2.x)) / 2 + ((v1.y - v2.y) * (v1.y + v2.y)) / 2,
			c = new Vertex((num0 * (v1.y - v2.y) - num1 * (v1.y - v0.y)) / denominator, (num1 * (v1.x - v0.x) - num0 * (v1.x - v2.x)) / denominator);

		circumcenters.push(c);
		return c;
	}

	function setCircumcenter(e) {
		var cc = circumcenter(e.dest(), e.org(), e.oNext().dest());
		circumcenters.push(cc);
		e.setLeft(cc);
		e.lNext().setLeft(cc);
		e.lPrev().setLeft(cc);
	}

	function insert(vertex) {
		if (!inCosmic(vertex)) {
			return;
		}

		var e = locate(vertex);
		if (!e) {
			return;
		}

		if (edge.colinearVertex(vertex)) {
			e = edge.oPrev();
			disconnect(edge);
			deleteQuadEdge(edge);
			edge = e;
		}
		e = getQuadEdge();

		var v = edge.org();

		edges.push(e);
		e.setOrgDest(v, vertex);
		e.splice(edge);

		do {
			e = connect(edge, e.sym());
			edges.push(e);
			edge = e.oPrev();
		} while (edge.dest() !== v);

		while (true) {
			e = edge.oPrev();
			if (edge.rightVertex(e.dest()) && inCircle(vertex, edge.org(), e.dest(), edge.dest())) {
				edge.swap();
				setCircumcenter(edge);
				edge = edge.oPrev();
			} else {
				if (edge.org() === v) {
					setCircumcenter(edge);
					return;
				}
				setCircumcenter(edge);
				edge = edge.oNext().lPrev();
			}
		}
	}

	function clamp(value, lower_bound, upper_bound) {
		return value < lower_bound ? lower_bound : value > upper_bound ? upper_bound : value;
	}

	function randomizeColorInc() {
		ri = Math.random() + 0.25;
		gi = Math.random() + 0.5;
		bi = Math.random() + 0.75;
	}

	function randomizeColors() {
		r = 255 * Math.random();
		g = 255 * Math.random();
		b = 255 * Math.random();
	}

	function getColor(cell) {
		var cr = Math.floor(cell + r),
			cg = Math.floor(cell + g),
			cb = Math.floor(cell + b);

		cr %= 255;
		cg %= 255;
		cb %= 255;

		return 'rgb(' + cr.toString() + ',' +  cg.toString() + ',' + cb.toString() + ')';
	}

	function drawTriangle(v0, v1, v2, color) {
		context.fillStyle = color;
		context.beginPath();
		context.moveTo(v0.x, v0.y);
		context.lineTo(v1.x, v1.y);
		context.lineTo(v2.x, v2.y);
		context.lineTo(v0.x, v0.y);
		context.closePath();
		context.fill();
	}

	function loop() {
		loopID = requestAnimationFrame(loop);

		var vertex,
			x,
			y,
			vx,
			vy,
			abs_vx,
			abs_vy,
			dx,
			dy,
			d,
			angle,
			cos_angle,
			sin_angle,
			a,
			i = totalVertices;

		initDelaunay();

		while (i--) {
			vertex = vertices[i];
			x = vertex.x;
			y = vertex.y;
			vx = vertex.vx;
			vy = vertex.vy;
			dx = x;
			dy = y;
			d = Math.sqrt(dx * dx + dy * dy);
			angle = Math.atan2(dy, dx);
			cos_angle = Math.cos(angle);
			sin_angle = Math.sin(angle);

			abs_vx = Math.abs(vx);
			abs_vy = Math.abs(vy);

			if (abs_vx < 0.1) {
				vx *= Math.random() * maxSpeed;
			} else if (abs_vx > maxSpeed) {
				vx *= 0.9;
			}

			if (abs_vy < 0.1) {
				vy *= Math.random() * maxSpeed;
			} else if (abs_vy > maxSpeed) {
				vy *= 0.9;
			}

			var next_x = x + vx,
				next_y = y + vy;

			if (next_x > canvasWidth) {
				next_x = canvasWidth;
				vx *= -1;
			} else if (next_x < 0) {
				next_x = 0;
				vx *= -1;
			}

			if (next_y > canvasHeight) {
				next_y = canvasHeight;
				vy *= -1;
			} else if (next_y < 0) {
				next_y = 0;
				vy *= -1;
			}

			if (!vx) {
				vx = 0;
			}
			if (!vy) {
				vy = 0;
			}

			vertex.vx = vx;
			vertex.vy = vy;
			vertex.x = next_x;
			vertex.y = next_y;
			vertex.cell = i;
			insert(vertex);
		}

		// Update colors
		if (b < 3) {
			randomizeColorInc();
		}
		r += ri;
		g += gi;
		b += bi;

		edges.each(function(edge) {
			var org = edge.org(),
				dest = edge.dest(),
				left = edge.left(),
				right = edge.right();

			if (!org.isInfinity && right && left) {
				drawTriangle(org, right, left, getColor(org.cell));
			}

			if (!dest.isInfinity && right && left) {
				drawTriangle(dest, left, right, getColor(dest.cell));
			}
		});
	}

	Voronoi.init = function(canvas, width, height) {
		context = canvas.getContext('2d');
		if (!context) {
			return;
		}

		canvasWidth = width || 80;
		canvasHeight = height || 80;

		var i = totalVertices;
		while (i--) {
			var vertex = new Vertex(Math.random() * canvasWidth, Math.random() * canvasHeight);
			vertex.vx = Math.cos(i) * Math.random() * maxSpeed;
			vertex.vy = Math.sin(i) * Math.random() * maxSpeed;
			vertices.push(vertex);
		}

		randomizeColors();
		randomizeColorInc();
	};

	Voronoi.stop = function() {
		cancelAnimationFrame(loopID);
	};

	Voronoi.start = function() {
		Voronoi.stop();
		loop();
	};

}(Voronoi));
