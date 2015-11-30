// Computer Science 854
// Homework #6
// Test File for (virtual) method resolution
// John Boyland
// Fall 2015

// This file is intended to provide some artificial tests
// to determine whether CHA and 0-CFA is implemented
// exactly according to the homework specifications.

// CHA example
// The example from the CHA paper

class A() extends IO() {
  def m() : Any = { out("A::m\n") };
  def n() : Any = { out("A::n\n") };
  def p() : Any = { out("A::p\n") };
}

class B() extends A() {
  override def m() : Any = { out("B::m\n") };
}

class C() extends A() {
  override def m() : Any = { out("C::m\n") };
}

class D() extends B() {
}

class E() extends C() {
  override def m() : Any = { out("E::m\n") };
}

class F() extends C() {
  override def p() : Any = { 
    out("F::p\n");
    m();                // self call to m
    this
  };
}

class G() extends F() {
  override def out(x : String) : IO = {
    super.out("G::out\n");
    super.out(x)
  };
}

class H() extends F() {
}

// 0-CFA should determine that this class is never instantiated
class Dead() extends IO() {
  var v : ArrayAny = new ArrayAny(-3);
  {
    v.set(0,new G())
  };
}

// Test that the non-null analysis specified
// along with CHA does the right thing.
// This class is dead code for 0-CFA.
class TestSimpleNullAnalysis() extends IO() {
  var i : Int = 0;
  var b : Boolean = true;
  var u : Unit = ();
  var s : String = "string";
  var o : Any = new Dead();
  var a : A = new A();
  var v : ArrayAny = new ArrayAny(10);
  {
    new G().p();  // calling a constructor

    i.toString(); // Integer type
    b.toString(); // Boolean type
    u.toString(); // Unit type
    s.toString(); // String type
    a.equals(5).toString(); // Boolean return value OK too
    out_any("hello".equals("bye")); // string literal is not null

    // block
    {}.toString(); // empty block (and Unit)
    { null; this }.equals(a); // non-empty block

    // let:
    { var unused : Null = null; new G() }.p();
    { var unused : Int = 5; s }.equals("bye");

    // if:
    { if (b) this else abort("won't happen") }.equals(o);
    { if (b) abort("won't happen") else new ArrayAny(10) }.get(3);
    { if (b) v else new ArrayAny(10) }.get(0);
    { if (b) new ArrayAny(0) else v }.get(10);
    { if (b) v else v }.get(0);

    // match
    o match {
      case b:B => b.p(); b
      case null => abort("null")
      case a:A => a.p(); out_any(a); this
    }.in();

    o match {
      case c:C => c.m(); c.out("test1")
    }.out("test2")
  };
}

class T1(var x : T2) {
  def f1() : Any = x.f2();
  def g1() : Any = f1();
}

class T2(var x : T3) {
  def f2() : Any = x.f3();
  def g2() : Any = new T1(this).g1();
}

class T3(var x : T4) {
  def f3() : Any = x.f4();
  def g3() : Any = new T2(this).g2();
}

class T4(var x : T5) {
  def f4() : Any = x.f5();
  def g4() : Any = new T3(this).g3();
}

class T5() {
  def f5() : Any = new G();
  def g5() : Any = new T4(this).g4();
}


class Ghost() extends IO() {
  var v : ArrayAny = new ArrayAny(100);
  {
    abort("Ghost class should not be instantiated actually");
    v.set(1,true)
  };
}

class Main() extends Statistics() {
  def dead() : Nothing = { 
    new Dead(); abort("Should never execute this code") 
  };

  var v : ArrayAny = new ArrayAny(0).resize(1).resize(10);
  var a : A = null;
  var o1 : Any = true;
  var o2 : Any = "unchanged\n";
  var o3 : Any = null;
  var b : Boolean = true;

  def live() : Any = {
    v.set(0,"Hello")
  };

  def two() : Int = 1 + {a = new H(); 1};

  // this method is never actually called,
  // but 0-CFA thinks it is.
  def ghost() : Any = {
    o2 = new Ghost();
    in().equals("--crash");
    ghost()
  };

  {
    out_any((if (b) "Hello" else o2).equals("test"));
    out(" ");
    out((!{o3 = o2; true}).toString());
    super.out("\n");
    while (!b) {
      o1 = ()
    };
    new T5().g5() match {
      case aa:A => v.set(two(),a); o1 = aa.p()
      case o:Any => dead()
      case null => dead()
    };
    o1 match {
      case c:C => c.out("G right?\n"); live()
      case x:IO => dead()
      case null => ghost()
      case u:Unit => abort("possible but not actual")
    };
    out(o2.toString());
    v.get(two()) match {
      case b:B => dead()
      case g:G => dead()
      case a:A => out("Jackpot: H\n")
      case null => abort("possible but not actual")
      case x:String => abort("possible but not actual")
      case u:Unit => dead()
      case b:Boolean => abort("possible but not actual") 
    }
  };

  {
    (o2 == o3).toString();
    symbol_name(symbol("None")).substring(1,3).charAt(1).toString()
  };

  {
    if ("--show-statistics".equals(in())) print() else ()
  };
}

