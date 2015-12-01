import scala.collection.mutable.Map
import scala.collection.mutable.Set
import scala.collection.mutable.MutableList

class Analysis(var program : Program, var options : CoolOptions, var next_node_id : Int) extends IO()
{

  def run() : Unit = {
    var analyses : String = options.get_analysis();
    while (!(analyses == "")) {
      var n : Int = analyses.length();
      var i : Int = analyses.indexOf(":");
      var analysis : String = analyses;
      if (i == -1) analyses = "" else {
        analysis = analyses.substring(0,i);
        analyses = analyses.substring(i+1,n)
      };
      n = analysis.length();
      if (matches(analysis,"resolve")) {
        var level : Int = 1; // default: CHA
        if (analysis == "resolve") ()
        else if (analysis == "resolve=none") level = 0
        else if (analysis == "resolve=cha") level = 1
        else if (analysis == "resolve=0cfa") level = 2
        else abort("unknown ".concat(analysis));
        if (0 < level) {
          var r : Resolution = new Resolution(program,level,next_node_id);
          r.run();
          next_node_id = r.get_next_node_id()
          if(options.get_analysis_debug) {
            r.report;
          }
        } else ()
      } else if (matches(analysis,"inline")) {
      } else if (matches(analysis,"dead")) {
      } else if (matches(analysis,"const-prop")) {
        var const : ConstantPropAnalysis = new ConstantPropAnalysis(program, next_node_id);
        const.run();
        next_node_id = const.get_next_node_id()
        
      } else {
        abort("unknown analysis ".concat(analysis))
      }
    };
    

    ()
  };

  def matches(s : String, p : String) : Boolean = {
    var n : Int = p.length();
    if (n <= s.length())
      s.substring(0,n) == p
    else false
  };

}

class AdditionalNodeFactory(var modifier : CoolTreeModifier, var nni : Int) extends CoolNodeFactory(nni) {
  override def get_line_number() : Int = modifier.get_line_number();
}

class AbstractOptimizer(var next_node_id : Int) extends CoolTreeModifier()
{
  var factory : CoolNodeFactory = new AdditionalNodeFactory(this,next_node_id);
  def get_next_node_id() : Int = factory.get_node_number();
}

class Resolution(var program : Program, var level : Int, var nni : Int)
extends AbstractOptimizer(nni)
{
  val cha = new ClassHirerachyAnalysis(program);
  val nullChecker = new NonNullVisitor();
  val cfa = new ControlFlowAnalysis(program);
  var dispatchNum = 0.0;
  var chaConvert = 0.0;
  var cfaConvert = 0.0;
  var methNum = 0.0;
  var methodRemoved = 0.0;
  var branchNum = 0.0;
  var branchRemoved = 0.0;
  def run() : Unit = {
    if (level == 2) {
      cfa.run
    }
    program.accept(this)
    ()
  };

  def report {
    val chaDis = chaConvert / dispatchNum * 100;
    val cfaDis = cfaConvert / dispatchNum * 100;
    val m = methodRemoved / methNum * 100;
    val c = branchRemoved / branchNum * 100;
    if(level == 1) {
      print("\nDispatch converted w/ CHA : ")
      print(chaDis)
      print(" %\n")
    } else if(level == 2) {
      print("\nDispatch converted w/ 0-CFA : ")
      print(cfaDis)
      print(" %\nMethod bodies omitted : ")
      print(m)
      print(" %\nCases omitted : ")
      print(c)
      print(" %\n")
    }
  }
  override def visit_dispatch(the_node:Cdispatch,expr:Expression,name:Symbol,actuals:Expressions) : Expression = {
    dispatchNum += 1;
    val newExpr = visit_Expression(expr);
    val newActuals = visit_Expressions(actuals);
    if(newExpr.of_type == name) {
      chaConvert += 1;
      cfaConvert += 1;
      val result = factory.static_dispatch(newExpr, newExpr.of_type, name,newActuals);
      result.set_of_type(the_node.get_of_type);
      result.set_mbinding(the_node.get_mbinding);
      result.set_line_number(the_node.get_line_number);
      return result
    }
    if(level == 1) {
    if(nullChecker.notNull(newExpr)) {
      val staticMethods = cha.overlapMethods(newExpr.of_type, name);
      if(staticMethods.size == 1){
        for( m <- staticMethods) {
          chaConvert += 1;
          val result = factory.static_dispatch(newExpr, m.klass, m.methodName,newActuals)
          result.set_of_type(the_node.get_of_type);
          result.set_mbinding(the_node.get_mbinding);
          result.set_line_number(the_node.get_line_number);
          return result
        }
      } 
    }
    the_node.set_expr(newExpr);
    the_node.set_actuals(newActuals);
    the_node
  } else if(level == 2) {
    val staticTypes = cfa.setE(expr.id)
    if(staticTypes.size == 1) {
      for( c <- staticTypes) {
        cfaConvert += 1;
        val Method(klass, _,cm) = cfa.findMethod(c, name)
        val result = factory.static_dispatch(newExpr, klass, name,newActuals);
        result.set_of_type(the_node.get_of_type);
        result.set_mbinding(cm);
        result.set_line_number(the_node.get_line_number);        
        return result
      }
    }

    the_node.set_expr(newExpr);
    the_node.set_actuals(newActuals);
    the_node
  } else {
    the_node.set_expr(newExpr);
    the_node.set_actuals(newActuals);
    the_node
  }
  }

  override def visit_method(the_node:Cmethod,overridep:Boolean,name:Symbol,formals:Formals,return_type:Symbol,expr:Expression) : Feature = {
    methNum += 1;
    val newFormals = visit_Formals(formals);
    var newExpr: Expression = null;
    
    if(level == 2){
      val set = cfa.setS(the_node.id)
      if(set.isEmpty && !expr.isInstanceOf[Cno_expr]) {
        val nilNode = factory.nil()
        nilNode.set_line_number(expr.get_line_number)
        nilNode.of_type = 'Null
        methodRemoved += 1;
        newExpr = nilNode
      } else{
        newExpr = visit_Expression(expr)
      }
    } else {
      newExpr = visit_Expression(expr)
    }
    
    the_node.set_formals(newFormals);
    the_node.set_expr(newExpr);
    the_node
  }
  
  override def visit_Cases_one(node:Case) : Cases = {
    branchNum += 1;
    line_number = node.get_line_number();
    var result : Cases = new Cases_one(visit_Case(node))
    if(level == 2){
      val set = cfa.setS(node.id)
      if(set.isEmpty) {
        branchRemoved += 1;
        result = new Cases_nil
        result.set_line_number(node.get_line_number)
        return result 
      }
    }
    result
  };
  
}

class ClassHirerachyAnalysis(val program : Program) extends IO {
  var cone = Map[Symbol, Set[Symbol]]();
  var applies_to = Map[MethodInfo, Set[Symbol]]();
  var allClasses = Set[Cclass_decl]();
  var allMethods = Set[RawMethodInfo]();
  var allMethodInfo = Set[MethodInfo]();
  val iOverridings = Map[MethodInfo, Set[MethodInfo]]();
  val roots = Set[MethodInfo]();
  val p = program.asInstanceOf[Cprogram];
  val ce = p.get_classes.elements;
  // collect whole program information about classes and methods
  while(ce.hasNext) ce.next match {
    case c : Cclass_decl => cone += c.get_name -> Set(c.get_name);
                            allClasses.add(c);
                            val fe = c.get_features.elements;
                            while(fe.hasNext) {
                            fe.next match {
                              case m : Cmethod => val this_method = RawMethodInfo(c, m.get_name, m.get_overridep);
                                                  if(c.get_name != m.get_name){
                                                    allMethods.add(this_method);
                                                    iOverridings += MethodInfo(c.get_name, m.get_name) -> Set[MethodInfo]();
                                                    if(!m.get_overridep) roots += MethodInfo(c.get_name, m.get_name);
                                                  }

                              case a : Cattr => ()
                            }
                          }
                        }
  // set all of the cone sets
  for(c <- allClasses) {
    var ss = allSuperClasses(c);
    for( s <- ss) {
      cone(s) += c.get_name
    }
  }

  allMethodInfo = allMethods.map((m) => MethodInfo(m.klass.get_name, m.methodName));
  for( m <- allMethods) {
    // set initial applies-to sets
    applies_to += MethodInfo(m.klass.get_name, m.methodName) -> coneSetOf(m.klass.get_name).clone
    // build the partial order
    if(m.overridep) {
      val c = m.klass;
      val cName = c.get_name;
      var superclass = c.get_superclass.asInstanceOf[Cclass_decl];
      while(!hasMethod(superclass, m.methodName) 
        && superclass.get_name != 'native) superclass = superclass.get_superclass.asInstanceOf[Cclass_decl];
      iOverridings(MethodInfo(superclass.get_name, m.methodName)) += MethodInfo(cName, m.methodName);
    }
  }
  // traverse the pratial order top-down to build applies-to sets
  for( m <- roots) {
    traverseOverride(m)
  }

  def overlapMethods(className: Symbol, methodName: Symbol): Set[MethodInfo] = {
    val inferredClasses = coneSetOf(className);
    val potentials = potentialMethods(className, methodName);
    val result = Set[MethodInfo]();
    for( m <- potentials) {
      if(!appliesToSetOf(m).intersect(inferredClasses).isEmpty) result += m
    }
    result
  }
  def potentialMethods(className: Symbol, methodName: Symbol): Set[MethodInfo] = {
    val m = MethodInfo(className, methodName);
    val subs = coneSetOf(className);
    val result = Set[MethodInfo]();
    for( c <- subs) {
      if(allMethodInfo.contains(MethodInfo(c, methodName))) result += MethodInfo(c, methodName);
    }
    if(!allMethodInfo.contains(m)){
      var superclass: Cclass_decl = allClasses.find((c) => c.get_name == className) match {
        case Some(sc) => sc.get_superclass.asInstanceOf[Cclass_decl]
        case None => null
      }
      while(!allMethodInfo.contains(MethodInfo(superclass.get_name, methodName)) && superclass.get_name != 'native){
        superclass = superclass.get_superclass.asInstanceOf[Cclass_decl]
      }
      result += MethodInfo(superclass.get_name, methodName)
    }
    result
  }
  def coneSetOf(className : Symbol): Set[Symbol] = cone(className)
  def appliesToSetOf(method : MethodInfo): Set[Symbol] = applies_to(method)

  def allSuperClasses(c : Cclass_decl) : Set[Symbol] = {
    val result = Set[Symbol]();
    var current_class = c;
    while(current_class.get_parent != 'native) {
      result += current_class.get_parent;
      current_class = current_class.get_superclass.asInstanceOf[Cclass_decl];
    }
    result
  }
  def hasMethod(c : Cclass_decl, name : Symbol): Boolean = {
    val fe = c.get_features.elements;
    var result = false;
    while(fe.hasNext) fe.next match {
      case m : Cmethod => if(m.get_name == name) result = true
      case _ : Cattr => ()
    }
    result
  }
  def traverseOverride(m: MethodInfo) {
    for( o <- iOverridings(m)) {
      applies_to(m) --= applies_to(o)
      traverseOverride(o)
    }
  }

  def findMethod(klass: Symbol, methodName: Symbol) : Cmethod = {
    var result : Cmethod = null;
    allClasses.find((c) => c.get_name == klass) match {
      case Some(k) => 
      val fe = k.get_features.elements
      while(fe.hasNext) {
        fe.next match {
          case m : Cmethod => result = m
          case a : Cattr => ()
        }
      }
      case None => abort("Error")
    }
    if(result == null){
      abort("Error")
    }
    result
  }
}

class NonNullVisitor() extends CoolVisitor {
  def notNull(e : Expression) : Boolean = {
    e.accept(this) match {
      case b : Boolean => b
    }
  }

  override def visit_Expression (n : Expression) = List('Int,'Boolean,'Unit, 'Nothing).contains(n.of_type)
  override def visit_variable(the_node:Cvariable,name:Symbol) = {
    val bind = the_node.get_binding
    if(name == 'this){
      true
    } else {
      bind match {
        case b : Cbranch => b.get_local_type() != 'Null
        case a : Any => List('Int,'Boolean,'Unit, 'Nothing).contains(the_node.of_type)
      }
    }
  };
  override def visit_alloc(the_node:Calloc,type_name:Symbol) = true;
  override def visit_dispatch(the_node:Cdispatch,expr:Expression,name:Symbol,actuals:Expressions) = 
    expr.of_type == name || List('Int,'Boolean,'Unit, 'Nothing).contains(the_node.of_type);
  override def visit_static_dispatch(the_node:Cstatic_dispatch,expr:Expression,type_name:Symbol,name:Symbol,actuals:Expressions) = 
    type_name == name || List('Int,'Boolean,'Unit, 'Nothing).contains(the_node.of_type)
  override def visit_block(the_node:Cblock,body:Expressions) = 
    body.size == 0 || body.nth(body.size - 1).accept(this).asInstanceOf[Boolean];
  override def visit_nil(the_node:Cnil) = false;
  override def visit_int_lit(the_node:Cint_lit,token:Symbol) = true; 
  override def visit_bool_lit(the_node:Cbool_lit,value:Boolean) = true;
  override def visit_string_lit(the_node:Cstring_lit,token:Symbol) = true;
  override def visit_let(the_node:Clet,identifier:Symbol,local_type:Symbol,init:Expression,body:Expression) = 
    body.accept(this).asInstanceOf[Boolean];
  override def visit_cond(the_node:Ccond,pred:Expression,then_exp:Expression,else_exp:Expression) = 
    then_exp.accept(this).asInstanceOf[Boolean] && else_exp.accept(this).asInstanceOf[Boolean];
  override def visit_branch(the_node:Cbranch,name:Symbol,local_type:Symbol,expr:Expression) = expr.accept(this);
  override def visit_typecase(the_node:Ctypecase,expr:Expression,cases:Cases) = {
     var result = true;
     val enum = cases.elements;
     while (enum.hasNext) {
      val n = enum.next
      result = result && n.accept(this).asInstanceOf[Boolean]
    }
    result
  } 
}

case class MethodInfo(klass: Symbol, methodName: Symbol);
case class RawMethodInfo(klass: Cclass_decl, methodName: Symbol, overridep: Boolean);

class ControlFlowAnalysis(program: Program) extends CoolVisitor {
  val setD = Map('Int -> 'Int, 'Unit -> 'Unit, 'Boolean -> 'Boolean).withDefaultValue('Null);
  var setS = Map[Int, Set[Symbol]]().withDefaultValue(Set[Symbol]());
  var setE = Map[Int, Set[Symbol]]().withDefaultValue(Set[Symbol]());
  val allClasses = Map[Symbol, Cclass_decl]();
  val allMethods = Set[MethodInfo]();
  val ms = Map[Int, MethodInfo]();
  var arraySetObj : Formal = null;

  collectInfo;

  def run() {
    program.accept(this)
    var olds = setS.clone;
    var olde = setE.clone;
    do {
      olds = setS.clone
      olde = setE.clone
      program.accept(this)
    } while(olds != setS || olde != setE) 
    do {
      olds = setS.clone
      olde = setE.clone
      program.accept(this)
    } while(olds != setS || olde != setE)

  }

  override def visit_program(the_node:Cprogram,classes:Classes) = {
    val ce = classes.elements;
    while(ce.hasNext) ce.next.accept(this)
  }
  override def visit_class_decl(the_node:Cclass_decl,name:Symbol,parent:Symbol,features:Features,filename:Symbol) = {
    val fe = features.elements;
    while(fe.hasNext) {
      fe.next match {
        case a : Cattr => a.accept(this)
        case c : Cmethod => 
      }
    }
    val fe1 = features.elements;
    while(fe1.hasNext) {
      fe1.next match {
        case a : Cattr => 
        case c : Cmethod => c.accept(this)
      }
      
    }
  }
  override def visit_method(the_node:Cmethod,overridep:Boolean,name:Symbol,formals:Formals,return_type:Symbol,expr:Expression) = {
    checkExist(the_node);
    val klass = the_node.get_owner.asInstanceOf[Cclass_decl]
    val fe = formals.elements;
    while(fe.hasNext){
      fe.next.accept(this);
    }

    if(expr.isInstanceOf[Cno_expr]) {
      setE(expr.id) = (klass.get_name, name) match {
        case ('Any, 'Any) => setS(sigmaOf(the_node))
        case ('Any, 'toString) => Set('String)
        case ('Any, 'equals) => Set('Boolean)
        case ('IO, 'abort) => Set[Symbol]()
        case ('IO, 'out) => setS(sigmaOf(the_node))
        case ('IO, 'in) => Set('String, 'Null)
        case ('IO, 'symbol) => Set('Symbol)
        case ('IO, 'symbol_name) => Set('String)
        case ('Unit, 'Unit) => Set('Unit)
        case ('Int, 'Int) => Set('Int)
        case ('Int, 'toString) => Set('String)
        case ('Int, 'equals) => Set('Boolean)
        case ('Boolean, 'Boolean) => Set('Boolean)
        case ('Boolean, 'equals) => Set('Boolean)
        case ('String, 'String) => Set('String)
        case ('String, 'equals) => Set('Boolean)
        case ('String, 'concat) => Set('String)
        case ('String, 'substring) => Set('String)
        case ('String, 'charAt) => Set('Int)
        case ('Symbol, 'Symbol) => Set('Symbol)
        case ('ArrayAny, 'ArrayAny) => setS(sigmaOf(the_node))
        case ('ArrayAny, 'resize) => setS(sigmaOf(the_node))
        case ('ArrayAny, 'get) => if(arraySetObj == null){
                                    Set('Null)
                                  } else {
                                    Set('Null).union(setS(arraySetObj.id))
                                  }
        case ('ArrayAny, 'set) => val fe = formals.elements;
                                  var snd_p : Formal = null;
                                  while(fe.hasNext) {
                                    snd_p = fe.next
                                  }
                                  arraySetObj = snd_p;
                                  Set('Null).union(setS(arraySetObj.id))
        case ('Statistics, 'clear) => setS(sigmaOf(the_node))
        case ('Statistics, 'get) => Set('Int)
        case ('Statistics, 'print) => setS(sigmaOf(the_node))
      }
      
    }
    

    // if(setS(sigmaOf(the_node)).isEmpty && !expr.isInstanceOf[Cno_expr]){
    if(!expr.isInstanceOf[Cno_expr]){
      val internal = new InternalCFA(program, setS, setE, arraySetObj, the_node)
      expr.accept(internal)
      if(klass.get_name == 'Main && name == 'Main) {
        setS(sigmaOf(the_node)) += 'Main
      }
      setS(the_node.id) = setE(expr.id)
      //if(the_node.id == 485) {print(setE(expr.id));print("\n\n")};
    } else {
      setS(the_node.id) = setE(expr.id);
    } 
  }
  override def visit_formal(the_node:Cformal,name:Symbol,of_type:Symbol)  = {
    checkExist(the_node);
  }
  override def visit_attr(the_node:Cattr,name:Symbol,of_type:Symbol) = {
    checkExist(the_node);
    setS(the_node.id) += setD(of_type)
  }

  override def visit_branch(the_node:Cbranch,name:Symbol,local_type:Symbol,expr:Expression) = {
    checkExist(the_node)
    expr.accept(this)
  }

  override def visit_assign(the_node:Cassign,name:Symbol,expr:Expression) = {
    expr.accept(this);
    val x = the_node.get_binding
    setS(x.id) ++= setE(expr.id);
    setE(the_node.id) = Set('Unit);
  }

  override def visit_dispatch(the_node:Cdispatch,expr:Expression,name:Symbol,actuals:Expressions) = {
    if(!setE.contains(the_node.id)) setE(the_node.id) = Set[Symbol]();
    expr.accept(this)
    val ae = actuals.elements
    val as = MutableList[Expression]();
    while(ae.hasNext) {
      val a = ae.next;
      a.accept(this)
      as += a
    }
    
    for( c <- setE(expr.id) if c != 'Null) {
      val klass = allClasses(c)
      val maybeMethod = m(klass, name)

      maybeMethod match {
        case Some(MethodType(runtime_method, ps, rTy)) => 
        setS(sigmaOf(runtime_method)) ++= Set(c)
        for( i <- 0 to (ps.size - 1)) {
          val (xi, ti) = ps(i)
          val ei = as(i)
          setS(xi.id) ++= setE(ei.id)
        }
        setE(the_node.id) ++= setS(runtime_method.id)

        case None => ()
      }
    }
    expr.accept(this)
  }

  override def visit_alloc(the_node:Calloc,type_name:Symbol) = {
    setE(the_node.id) = Set(type_name)
  }

  override def visit_cond(the_node:Ccond,pred:Expression,then_exp:Expression,else_exp:Expression) = {
    pred.accept(this)
    then_exp.accept(this)
    else_exp.accept(this)
    setE(the_node.id) = setE(then_exp.id).union(setE(else_exp.id))
  }

  override def visit_loop(the_node:Cloop,pred:Expression,body:Expression) = {
    pred.accept(this)
    body.accept(this)
    setE(the_node.id) = Set('Unit)
  }

  override def visit_typecase(the_node:Ctypecase,expr:Expression,cases:Cases) = {
    if(!setE.contains(the_node.id)) setE(the_node.id) = Set[Symbol]();
    expr.accept(this)
    val be = cases.elements
    val test = hasNull(cases)
    val containNull = setE(expr.id).contains('Null)

    if(containNull && test != None){
      test match {
        case Some((xi, ei)) =>
        //print(xi.get_line_number)
        //print(xi)
        //print("\n\n")
        xi.accept(this)
        setS(xi.id) += 'Null
        setE(the_node.id) ++= setE(ei.id)
        case None =>
      }
    }
      for( c <- setE(expr.id) if c != 'Null) {
        val actualType = minType(c, cases)
        match {
          case Some(b) => 
          //print(b.get_line_number)
          //print(b)
          //print("\n\n")
          b.accept(this)
          setS(b.id) += c
          setE(the_node.id) ++= setE(b.get_expr.id)
          case None => ()
        }
      }
  }

  override def visit_block(the_node:Cblock,body:Expressions) = {
    val be = body.elements
    var result = Set('Unit);
    while(be.hasNext) {
      val e = be.next
      e.accept(this)
      result = setE(e.id)
    }
    setE(the_node.id) = result
  }

  override def visit_let(the_node:Clet,identifier:Symbol,local_type:Symbol,init:Expression,body:Expression) = {
    checkExist(the_node)
    init.accept(this)
    body.accept(this)
    setS(the_node.id) = setE(init.id)
    setE(the_node.id) = setE(body.id)
  }

  override def visit_add(the_node:Cadd,e1:Expression,e2:Expression) = {
    e1.accept(this)
    e2.accept(this)
    setE(the_node.id) = Set('Int)
  }

  override def visit_sub(the_node:Csub,e1:Expression,e2:Expression) = {
    e1.accept(this)
    e2.accept(this)
    setE(the_node.id) = Set('Int)
  }

  override def visit_mul(the_node:Cmul,e1:Expression,e2:Expression) = {
    e1.accept(this)
    e2.accept(this)
    setE(the_node.id) = Set('Int)
  }

  override def visit_div(the_node:Cdiv,e1:Expression,e2:Expression) = {
    e1.accept(this)
    e2.accept(this)
    setE(the_node.id) = Set('Int)
  }

  override def visit_neg(the_node:Cneg,e1:Expression) = {
    e1.accept(this)
    setE(the_node.id) = Set('Int)
  }

  override def visit_lt(the_node:Clt,e1:Expression,e2:Expression) = {
    e1.accept(this)
    e2.accept(this)
    setE(the_node.id) = Set('Boolean)
  }

  override def visit_leq(the_node:Cleq,e1:Expression,e2:Expression) = {
    e1.accept(this)
    e2.accept(this)
    setE(the_node.id) = Set('Boolean)
  }

  override def visit_comp(the_node:Ccomp,e1:Expression) = {
    e1.accept(this)
    setE(the_node.id) = Set('Boolean)
  }

  override def visit_int_lit(the_node:Cint_lit,token:Symbol) = {
    setE(the_node.id) = Set('Int)
  }

  override def visit_bool_lit(the_node:Cbool_lit,token:Boolean) = {
    setE(the_node.id) = Set('Boolean)
  }

  override def visit_string_lit(the_node:Cstring_lit,token:Symbol) = {
    setE(the_node.id) = Set('String)
  }

  override def visit_nil(the_node:Cnil) = {
    setE(the_node.id) = Set('Null)
  }

  override def visit_unit(the_node:Cunit) = {
    setE(the_node.id) = Set('Unit)
  }

  override def visit_no_expr(the_node:Cno_expr) = {
    abort("Never visit Native")
  }

  def m(klass: Cclass_decl, methodName: Symbol): Option[MethodType] = {
    var sc = klass;
    var result : Option[MethodType] = None;
    while(sc != null && !allMethods.contains(MethodInfo(sc.get_name,methodName))){
      sc = sc.get_superclass.asInstanceOf[Cclass_decl]
    }
    if(sc == null) {
      return result;
    }
    val fe = sc.get_features.elements
    while(fe.hasNext){
      fe.next match {
        case m : Cmethod => if(m.get_name == methodName){
                              checkExist(m)
                              val acc = MutableList[(Formal, Symbol)]()
                              val fse = m.get_formals.elements
                              while(fse.hasNext) {
                                val f = fse.next.asInstanceOf[Cformal]
                                checkExist(f)
                                acc += ((f, f.get_of_type))
                              }
                              result = Some(MethodType(m,acc, m.get_return_type));
                            }
        case a : Cattr => ()
      }
    }
    result
  }

  def findMethod(c : Symbol, methodName: Symbol): Method = {
    val klass = allClasses(c);
    var result : Method = null;
    m(klass, methodName) match {
      case Some(MethodType(cm, _, _)) => 
      val owner = cm.get_owner.get_name
      result = Method(owner, methodName,cm)
      case None => abort("Error: No method")
    }
    result
  }

  def checkExist(n: CoolNode) = {
    if(!setS.contains(n.id)) {
      setS(n.id) = Set[Symbol]();
    }
  }

  def collectInfo {
    val cp = program.asInstanceOf[Cprogram];
    val ce = cp.get_classes.elements;
    while(ce.hasNext) {
      val c = ce.next.asInstanceOf[Cclass_decl];
      allClasses += c.get_name -> c;
      val fe = c.get_features.elements;
      while(fe.hasNext){
        fe.next match {
          case m : Cmethod => ms += -m.id -> MethodInfo(c.get_name, m.get_name);
          case a : Cattr => ()
        }
      }
    }
    for( (k, v) <- ms) {
      setS(k) = Set[Symbol]();
      allMethods += v
    }
  }
  def sigmaOf(m : Cmethod) = {
    - m.id
  }

  def hasNull(cs : Cases): Option[(Cbranch, Expression)] = {
    val ce = cs.elements
    var result : Option[(Cbranch, Expression)] = None
    while(ce.hasNext) {
      val branch = ce.next.asInstanceOf[Cbranch]
      if(branch.get_local_type == 'Null){
        result = Some((branch, branch.get_expr))
      }
    }
    result
  }
  def allSuperClasses(c : Cclass_decl) : Set[Symbol] = {
    val result = Set(c.get_name);
    var current_class = c;
    while(current_class.get_parent != 'native) {
      result += current_class.get_parent;
      current_class = current_class.get_superclass.asInstanceOf[Cclass_decl];
    }
    result
  }
  def minType(c: Symbol, cases : Cases) : Option[Cbranch] = {
    val klass = allClasses(c);
    val be = cases.elements
    val allT = Set[Symbol]();
    while(be.hasNext) {
      val b = be.next.asInstanceOf[Cbranch]
      allT += (b.get_local_type)
    }
    val superclasses = allSuperClasses(klass)
    val tis = superclasses.intersect(allT)
    if (tis.isEmpty) {
      return None
    } else {
      val mc = tis.minBy[Int]((c) => -distance(allClasses(c)));
      val ce = cases.elements
      while(ce.hasNext) {
        val c = ce.next.asInstanceOf[Cbranch]
        if(c.get_local_type == mc) {
          return Some(c)
        }
      }
      None 
    }
  }

  def distance(c : Cclass_decl): Int = {
    var count = 0;
    var superclass = c;
    while(superclass.get_name != 'Any) {
      count += 1
      superclass = superclass.get_superclass.asInstanceOf[Cclass_decl]
    }
    count
  }
}

class InternalCFA(program : Program, s: Map[Int, Set[Symbol]], e: Map[Int, Set[Symbol]], obj: Formal, outer: Cmethod) extends ControlFlowAnalysis(program) {
  setS = s
  setE = e
  arraySetObj = obj
  override def visit_static_dispatch(the_node:Cstatic_dispatch,expr:Expression,type_name:Symbol,name:Symbol,actuals:Expressions) = {
    val mbinding = the_node.get_mbinding.asInstanceOf[Cmethod]
    checkExist(mbinding)
    val tTy = mbinding.get_return_type
    val ps = MutableList[(Cformal, Symbol)]()
    expr.accept(this)
    val ae = actuals.elements
    val as = MutableList[Expression]();
    while(ae.hasNext) {
      val a = ae.next;
      a.accept(this)
      as += a
    }
    val fe = mbinding.get_formals.elements
    while(fe.hasNext) {
      val f = fe.next.asInstanceOf[Cformal]
      checkExist(f)
      ps += ((f, f.get_of_type))
    }

    setS(sigmaOf(mbinding)) ++= setS(sigmaOf(outer))
    for( i <- 0 to (ps.size - 1)) {
      val (xi, ti) = ps(i)
      val ei = as(i)
      setS(xi.id) ++= setE(ei.id)
    }
    setE(the_node.id) = setS(mbinding.id)
  }

  override def visit_variable(the_node:Cvariable,name:Symbol) = {
    if(name == 'this){
      val klass = outer.get_owner.asInstanceOf[Cclass_decl]
      setE(the_node.id) = Set(klass.get_name)
    } else {
      val x = the_node.get_binding
      setE(the_node.id) = setS(x.id)
    }
  }
}

case class MethodType(the_node: Cmethod, parameters: MutableList[(Formal, Symbol)], returnType: Symbol);
case class Method(klass: Symbol, methodName: Symbol, m: Cmethod)
