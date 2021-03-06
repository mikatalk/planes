(function ( $ ) {
  
  var planes = []
  , currentPlane = -1
  , currentcorner = -1;

  initialize();

  $.fn.project = function( options ) {

    return this.each(function() {
      
      var offsetX = 100*Math.random();
      var offsetY = 100*Math.random();
      var plane = new Plane(this, 
        [
          75+Math.random()*100+offsetX, 50+Math.random()*100+offsetY, 
          350+Math.random()*100+offsetX, 70+Math.random()*100+offsetY,
           100+Math.random()*100+offsetX, 350+Math.random()*100+offsetY,
            300+Math.random()*100+offsetX, 280+Math.random()*100+offsetY
        ]
      );
      
      planes.push(plane);

      currentPlane = planes.length - 1;
      
      $(this)
        .wrap("<div class='plane " + ("plane-"+planes.length) + "'></div>")
        .css("border", "0.09em solid red")
        .css("position", "absolute");

      $(plane.el)
        .css("transform-origin", "0 0")
        .css("-webkit-transform-origin", "0 0")
        .css("-moz-transform-origin", "0 0")
        .css("-o-transform-origin", "0 0");

      var $wrap = $(".plane.plane-"+planes.length);

      $wrap.append(plane.marker0);
      $wrap.append(plane.marker2);
      $wrap.append(plane.marker4);
      $wrap.append(plane.marker6);

      $wrap.data("plane", planes.length)//.addClass("plane-"+planes.length);

      update();

    });


  };

// function addPlane()
  function initialize(){
    window.addEventListener('load', handleLoad);
    window.addEventListener('mousedown', handleMouseDown);
    window.addEventListener('mouseup', handleMouseUp);
    window.addEventListener('mousemove', move);
    console.log("initialized plugin");
  }
  
  /** Plane definition **/
  function Plane (el, corners) {
    this.corners = corners;
    this.el = el;
    var markerStyle="width:20px;margin-left:-10px;height:20px;margin-top:-10px;"
      + "display:block; position:absolute;background:#c3c3c3;border-radius: 10px;"
      + "border: 1px solid #333333;opacity: 0.5;cursor: cell;";
    this.marker0 = $("<div class='marker marker0' style='"+markerStyle+"'></div>");
    this.marker2 = $("<div class='marker marker2' style='"+markerStyle+"'></div>");
    this.marker4 = $("<div class='marker marker4' style='"+markerStyle+"'></div>");
    this.marker6 = $("<div class='marker marker6' style='"+markerStyle+"'></div>");
  }  

  
  
  /** Events **/
  function update() {
    if ( currentPlane == -1 ) return;

    var corners = planes[currentPlane].corners;
    transform2d(planes[currentPlane].el, corners[0], corners[1], corners[2], corners[3],
                     corners[4], corners[5], corners[6], corners[7]);
    for (var i = 0; i != 8; i += 2) {
      var elt = planes[currentPlane]['marker'+i].get(0);//$(el).parent().find(".marker"+i).get(0);//document.getElementById("marker" + i);
      elt.style.left = corners[i] + "px";
      elt.style.top = corners[i + 1] + "px";
    }
  }
  function move(evnt) {
    if ( currentPlane == -1 ) return;
    if (currentcorner < 0) return;
    planes[currentPlane].corners[currentcorner] = evnt.pageX;
    planes[currentPlane].corners[currentcorner + 1] = evnt.pageY;
    update();
  }
  function handleLoad(evnt) {
    document.documentElement.style.margin="0px";
    document.documentElement.style.padding="0px";
    document.body.style.margin="0px";
    document.body.style.padding="0px";
    update();
  }
  function handleMouseDown(evnt) {
    // if ( $(evnt.target).hasClass())
    var $target = $(evnt.target).parent(".plane");
    currentPlane = $target.data("plane" ) - 1;
    if ( currentPlane == undefined ) return;
    if ( typeof planes[currentPlane] === 'undefined' ) return;
    if ( currentPlane < 0 ) return;
    // bring child over top
    $('body').append($(planes[currentPlane].el).parent());


    var x = evnt.pageX, y = evnt.pageY, dx, dy;
    var best = 50; // 20px grab radius
    currentcorner = -1;


    for (var i = 0; i != 8; i += 2) {
      dx = x - planes[currentPlane].corners[i];
      dy = y - planes[currentPlane].corners[i + 1];
      if (best > dx*dx + dy*dy) {
        best = dx*dx + dy*dy;
        currentcorner = i;
      }
    }

        console.log("---", currentPlane, currentcorner)

    move(evnt);
  }
  function handleMouseUp(evnt) {
    currentcorner = -1;
    currentPlane = -1;
  }
 

  /** Math Magic provided by Martin von Gagern
   * site : martin.von-gagern.net
   * stackexchange: http://math.stackexchange.com/questions/296794/
   * demo: http://jsfiddle.net/dFrHS/1/
   **/
  // Compute the adjugate of m
  function adj(m) { 
    return [
      m[4]*m[8]-m[5]*m[7], m[2]*m[7]-m[1]*m[8], m[1]*m[5]-m[2]*m[4],
      m[5]*m[6]-m[3]*m[8], m[0]*m[8]-m[2]*m[6], m[2]*m[3]-m[0]*m[5],
      m[3]*m[7]-m[4]*m[6], m[1]*m[6]-m[0]*m[7], m[0]*m[4]-m[1]*m[3]
    ];
  }
  // multiply two matrices
  function multmm(a, b) { 
    var c = Array(9);
    for (var i = 0; i != 3; ++i) {
      for (var j = 0; j != 3; ++j) {
        var cij = 0;
        for (var k = 0; k != 3; ++k) {
          cij += a[3*i + k]*b[3*k + j];
        }
        c[3*i + j] = cij;
      }
    }
    return c;
  }
  // multiply matrix and vector
  function multmv(m, v) {
    return [
      m[0]*v[0] + m[1]*v[1] + m[2]*v[2],
      m[3]*v[0] + m[4]*v[1] + m[5]*v[2],
      m[6]*v[0] + m[7]*v[1] + m[8]*v[2]
    ];
  }
  function pdbg(m, v) {
    var r = multmv(m, v);
    return r + " (" + r[0]/r[2] + ", " + r[1]/r[2] + ")";
  }
  function basisToPoints(x1, y1, x2, y2, x3, y3, x4, y4) {
    var m = [
      x1, x2, x3,
      y1, y2, y3,
       1,  1,  1
    ];
    var v = multmv(adj(m), [x4, y4, 1]);
    return multmm(m, [
      v[0], 0, 0,
      0, v[1], 0,
      0, 0, v[2]
    ]);
  }
  function general2DProjection(
    x1s, y1s, x1d, y1d,
    x2s, y2s, x2d, y2d,
    x3s, y3s, x3d, y3d,
    x4s, y4s, x4d, y4d
  ) {
    var s = basisToPoints(x1s, y1s, x2s, y2s, x3s, y3s, x4s, y4s);
    var d = basisToPoints(x1d, y1d, x2d, y2d, x3d, y3d, x4d, y4d);
    return multmm(d, adj(s));
  }
  function project(m, x, y) {
    var v = multmv(m, [x, y, 1]);
    return [v[0]/v[2], v[1]/v[2]];
  }
  function transform2d(elt, x1, y1, x2, y2, x3, y3, x4, y4) {
    var w = elt.offsetWidth, h = elt.offsetHeight;
    var t = general2DProjection
      (0, 0, x1, y1, w, 0, x2, y2, 0, h, x3, y3, w, h, x4, y4);
    for(i = 0; i != 9; ++i) t[i] = t[i]/t[8];
    t = [t[0], t[3], 0, t[6],
         t[1], t[4], 0, t[7],
         0   , 0   , 1, 0   ,
         t[2], t[5], 0, t[8]];
    t = "matrix3d(" + t.join(", ") + ")";
    elt.style["-webkit-transform"] = t;
    elt.style["-moz-transform"] = t;
    elt.style["-o-transform"] = t;
    elt.style.transform = t;
  }
}( jQuery ));

