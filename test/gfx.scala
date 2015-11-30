// GFX.COOL
// Simple CS 351 graphics demo classes rewritten for Cool.
// rewritten for Cool 2009
// Version 1.1

class Useful() extends IO()
{
  def and(b1 : Boolean, b2 : Boolean) : Boolean =
    if (b1) b2 else false;
}

class Canvas(var width : Int, var height : Int) extends Useful()
{
  
  var marks : ArrayAny = new ArrayAny(width); // Array of Array of String
  
  {
    var i : Int = 0;
    while (i < width) {
      var a : ArrayAny = new ArrayAny(height);
      marks.set(i,a);
      var j : Int = 0;
      while (j < height) {
	a.set(j," ");
	j = j + 1
      };
      i = i + 1
    }
  };
  
  def get_width() : Int = width;
  def get_height() : Int = height;
  
  def get_column(x : Int) : ArrayAny =
    marks.get(x) match {
      case a:ArrayAny => a
    };

  def mark(x : Int, y : Int, c : Color) : Canvas = {
    // clip off points outside canvas
    if (and(and(0 <= x,x < width),and(0 <= y, y < height))) {
      get_column(x).set(y,c.get_shade()); this
    } else this
  };

  def dump_ascii(io : IO) : IO = {
    var j : Int = height-1;
    while (0 <= j) {
      var i : Int = 0;
      while (i < width) {
	get_column(i).get(j) match {
	  case s:String => io.out(s)
	};
	i = i + 1
      };
      io.out("\n");
      j = j-1
    };
    io
  };
}

class Color(var shade : String)
{
  def get_shade() : String = shade;
}

class Delta(var dx : Int, var dy : Int) extends Useful()
{

  def get_delta_x() : Int = dx;
  def get_delta_y() : Int = dy;
  
  def add(d : Delta) : Delta = {
    dx = dx + d.get_delta_x();
    dy = dy + d.get_delta_y();
    this
  };
  
  def plus(d : Delta) : Delta = {
    new Delta(dx + d.get_delta_x(),
	      dy + d.get_delta_y())
  };
  
  def divide(i : Int) : Delta = {
    new Delta(dx / i,dy / i)
  };
  
  override def equals(other : Any) : Boolean = {
    other match {
      case d : Delta =>
	and(dx == d.get_delta_x(),
	    dy == d.get_delta_y())
      case o:Any => false
    }
  };
}

class Shape(var color : Color) extends Useful()
{
  
  def get_color() : Color = color;
  
  def draw(c : Canvas) : Canvas = abort("draw is abstract");
  
  def move(d : Delta) : Shape = abort("move is abstract");

}

class Point(var c : Color, var x : Int, var y : Int)
extends Shape(c)
{
  def get_x() : Int = x;
  def get_y() : Int = y;

  override def draw(can:Canvas) : Canvas = {
    can.mark(x,y,color)
  };

  override def move(d:Delta) : Point = {
    x = x + d.get_delta_x();
    y = y + d.get_delta_y();
    this
  };
  
  def plus(d:Delta) : Point = {
    new Point(color,x,y).move(d)
  };
  
  def minus(p:Point) : Delta = {
    new Delta(x-p.get_x(),y-p.get_y())
  };
  
  override def equals(o : Any) : Boolean = {
    o match {
      case p : Point => and(x==p.get_x(),y==p.get_y())
      case oo : Any => false
    }
  };
}

class CenteredShape(var c : Color, var center : Point) extends Shape(c)
{
  def get_center() : Point = center;

  override def move(d:Delta) : CenteredShape = {
    center = center.plus(d); this
  };
}

class Group() extends
CenteredShape(new Color(" "),new Point(new Color(" "),0,0)) 
{
  var shapes : ArrayList = new ArrayList();
  
  def get(i : Int) : CenteredShape = {
    shapes.get(i) match {
      case s:CenteredShape => s
    }
  };
  
  def add(s : CenteredShape) : Group = {
    shapes.add(s);
    compute_center();
    this
  };
  
  def compute_center() : Point = {
    var n : Int = shapes.size();
    var origin : Point = new Point(color,0,0);
    var sum : Delta = new Delta(0,0); 
    var i : Int = 0;
    while (i < n) {
      var p1 : Point = get(i).get_center();
      sum.add(p1.minus(origin));
      i = i+1
    };
    if (0 < n) {
      center = origin.move(sum.divide(n)); center
    } else {
      center // unchanged
    }
  };
  
  override def move(d:Delta) : Group = {
    super.move(d);
    var n : Int = shapes.size();
    var i : Int = 0;
    while (i < n) {
      get(i).move(d);
      i = i+1
    };
    this
  };
  
  override def draw(can:Canvas) : Canvas = {
    var n : Int = shapes.size();
    var i : Int = 0; 
    while (i < n) {
      get(i).draw(can);
      i = i+1
    };
    can
  };
}  
  
class Line(var cl:Color, var p1:Point, var p2:Point) 
extends CenteredShape(cl,p1.plus(p2.minus(p1).divide(2)))
{
  var length : Int = 0;
  var horiz : Boolean = false;

  {
    horiz = p1.get_y() == p2.get_y();
    if (horiz) {
      length = p1.get_x() - p2.get_x()
    } else {
      length = p1.get_y() - p2.get_y();
      if (!(p1.get_x() == p2.get_x())) {
	abort("Error: Only horizontal and vertical lines supported")
      } else ()
    };
    length = if (length < 0) -length else length
  };

  def get_length() : Int = length;
  def get_horizontal() : Boolean = horiz;

  def get_point1() : Point =
    center.plus(new Delta(if (horiz) -length / 2 else 0,
                          if (horiz) 0 else -length / 2));


  def get_point2() : Point =
    center.plus(new Delta(if (horiz) length+-length / 2 else 0,
                          if (horiz) 0 else length+-length / 2));

  override def draw(can:Canvas) : Canvas = {
    var p : Point = get_point1();
    var pend : Point = get_point2();
    var d : Delta = new Delta(if (horiz) 1 else 0,
			      if (horiz) 0 else 1); 
    p.draw(can);
    while (!(p == pend)) {
      p.move(d);
      p.draw(can)
    };
    can
  };
}

class Rectangle(var cl:Color, var cp:Point, 
		var width:Int, var height:Int)
extends CenteredShape(cl,cp)
{

  def get_width() : Int = width;
  def get_height() : Int = height;

  def get_lower_left() : Point = {
   get_center().plus(new Delta(-width / 2, -height / 2))
  };

  def get_lower_right() : Point = {
   get_center().plus(new Delta(width-width / 2, -height / 2))
  };

  def get_upper_left() : Point = {
   get_center().plus(new Delta(-width / 2, height-height / 2))
  };

  def get_upper_right() : Point = {
   get_center().plus(new Delta(width-width / 2, height-height / 2))
  };
  
  override def draw(can:Canvas) : Canvas = {
    var ll : Point = get_lower_left();
    var lr : Point = get_lower_right();
    var ul : Point = get_upper_left();
    var ur : Point = get_upper_right(); 

    new Line(color,ul,ur).draw(can);
    new Line(color,ll,lr).draw(can);
    new Line(color,ll,ul).draw(can);
    new Line(color,lr,ur).draw(can)
  };
}


class Square(var cs:Color, var cps:Point, var size:Int) 
extends Rectangle(cs,cps,size,size)
{
  def get_size() : Int = size;
}


class  Block(var cb : Color, var p : Point, var w : Int, var h : Int) 
extends Rectangle(cb,p,w,h)
{
  // create block (filled rectangle)
  // with given center and width and height.

  override def draw(can : Canvas) : Canvas = {
    var ul : Point = get_upper_left();
    var l : Point = get_lower_left();
    var r : Point = get_lower_right();
    var up1 : Delta = new Delta(0,1);

    while (l.get_y() <= ul.get_y()) {
      new Line(color,l,r).draw(can);
      l.move(up1);
      r.move(up1);
      this
    };
    can
  };
}

class Main() extends Statistics()
{
  var white : Color = new Color(" ");
  var gray1 : Color = new Color("`");
  var gray2 : Color = new Color("^");
  var gray3 : Color = new Color("C");
  var gray4 : Color = new Color("X");
  var gray5 : Color = new Color("@");
  var gray6 : Color = new Color("M");
  var gray7 : Color = new Color("#");

  var canvas : Canvas = new Canvas(79,40);

  {    
    var g:Group = new Group();
    g.add(new Line(gray4,new Point(gray4,7,0),new Point(gray4,50,0)));
    g.add(new Line(gray5,new Point(gray5,50,4),new Point(gray5,50,40)));
    g.add(new Block(gray6,new Point(gray6,60,18),28,7));
    g.add(new Line(gray1,new Point(gray1,7,1),new Point(gray1,7,15)));
    g.draw(canvas)
  };
    
  {
    var g:Group = new Group();
    g.add(new Rectangle(gray3,new Point(gray3,40,15),50,5));
    g.add(new Square (gray2, new Point(gray2,20,20),10));
    g.draw(canvas);

    var d : Delta = new Delta(30,-10);
    g.move(d);
    g.draw(canvas);
    g.move(d);
    g.draw(canvas);
    g.move(d);
    g.draw(canvas);

    canvas.dump_ascii(this); if ("--show-statistics" == in()) print() else ()
  };
}

//ArrayList class manages a hybrid list with a dynamic array that
//doubles in capacity when growing.
class ArrayList() extends IO()
{

  var array : ArrayAny = new ArrayAny(1);	// the actual data values
  var size : Int = 0;	// the numbers of values used (not the capacity)

  //Add an item to the } of the list
  def add(item : Any) : ArrayList = { 
    insert(size, item)
  };

  //Given an index, returns the item stored at that index. 
  //Reports error for bad indices
  def get(index : Int) : Any = {
    if (index < 0) {
      abort ("ArrayList.get: negative index")
    } else {
      if (size <= index) {
	abort ("ArrayList.get: index too large")
      } else {
	array.get(index)
      }
    }
  };

  //Given an index, replaces the item stored at that index with the provided item
  //Reports error for bad indices
  def set(index : Int, item : Any) : Any = {
    if (index < 0) {
      abort ("ArrayList.set: negative index")
    } else {
      if (size <= index) {
	abort ("ArrayList.set: index too large")
      } else {
	array.set(index,item)
      }
    }
  };

  //Returns the number of items stored in the ArrayList
  def size(): Int = size;

  //Changes the size (number of elements stored) of the ArrayList to the number
  //provided.  May grow the capacity to encompass a larger size, but never 
  //reduces capacity.  Reports negative size errors.
  def resize(n : Int) : ArrayList = {
    if (n < 0) {
      abort ("ArrayList.resize: negative size")
    } else ();
    while (array.length() < n) {
      array = array.resize(array.length() * 2)
    };
    while (size < n) {
      array.set(size, null);
      size = size + 1
    };
    size = n;
    this
  };

  //Inserts the provided item at the provied position.  Increases size (and
  //capacity) as necessary.  Reports bad index errors
  def insert(index: Int, item : Any) : ArrayList = {
    if (index < 0) {
        abort ("ArrayList.insert: negative index")
    } else {
      if (size < index) {
	abort ("ArrayList.insert: index too large")
      } else {
	size = size + 1;
	resize(size);
	var j : Int = size - 1;
	while (index < j) {
	  array.set(j, array.get(j-1));
	  j = j - 1
	};
	array.set(index, item)
      }
    };
    this
  };
}
