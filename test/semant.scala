class CoolParserBase() extends CoolNodeFactory(0) {}
class Semant(var program : Program, var options : CoolOptions)
extends CoolVisitor()
{
  var io : IO = new IO();
  var errors : SemantErrors = new SemantErrors(options);
  var class_table : ClassTable = null;

  def run() : Boolean = {
    program.accept(this);
    !errors.has_errors()
  };

  var any_sym : Symbol = io.symbol("Any");

  // #(
  def consym(s : String, sym : Symbol) : String =
    s.concat(sym.toString().concat("'"));

  var nothing_sym : Symbol = io.symbol("Nothing");
  var symbol_sym : Symbol = io.symbol("Symbol");
  var native_sym : Symbol = io.symbol("native");
  var null_sym : Symbol = io.symbol("Null");

  var any_class_info : ClassInfo = null;
  var root_methods : MethodTable = new MethodTable();
  var root_environment : Environment = null;
  var feature_tables_ready : Boolean = false;
  // #)

  override def visit_program(the_node:Cprogram,classes:Classes) : Any = {
    class_table = new ClassTable(classes,errors);

    classes.accept(this);
    // In PA4 - you need to set program attributes
    //@(
    any_class_info = class_table.lookup(any_sym);
    root_environment = new RootEnvironment(class_table,errors);
    any_class_info.build_feature_tables(0,root_methods,root_environment);
    classes.accept(this);
    feature_tables_ready = true;
    classes.accept(this);
    //@)
    //#(
    // In PA5 - you need to arrange checks for circular inheritance etc,
    //          check for Main
    the_node.set_any_class(class_table.lookup_class(any_sym));
    the_node.set_int_class(class_table.lookup_class(int_sym));
    the_node.set_unit_class(class_table.lookup_class(unit_sym));
    the_node.set_boolean_class(class_table.lookup_class(bool_sym));
    the_node.set_string_class(class_table.lookup_class(string_sym));
    //#)

    //@(
    var mainsym : Symbol = symbol("Main");
    var main_class_info : ClassInfo = class_table.lookup(mainsym);
    var main_class : Cclass_decl = main_class_info.get_class_decl();
    if (is_null(main_class)) {
      var firstclass : Cclass_decl = classes.nth(8) match {
	case cd:Cclass_decl => cd
      };
      errors.error(firstclass,firstclass,"No Main class defined")
    } else if (0 < main_class_info.lookup_method(mainsym).get_formals().size()) {
      errors.error(main_class,main_class,"Main not allowed to have formals")
    } else
    //@)
    ()
  };

  override def visit_Classes_one(node:Class) : Any = node.accept(this);
  override def visit_class_decl(cd:Cclass_decl,name:Symbol,parent:Symbol,
                                features:Features,filename:Symbol) : Any = {
    // for PA4, check that name is not illegal
    // #(
    if (name == nothing_sym)
	errors.error(cd,cd,"Cannot declare class Nothing")
    else if (name == null_sym) 
        errors.error(cd,cd,"Cannot declare class Null")
    else ();
    // #)
    // for PA5, check superclass, inheritance (##)
    // @(
    var this_info : ClassInfo = class_table.lookup(name);
    var super_info : ClassInfo = class_table.lookup(parent);
    if (io.is_null(any_class_info)) {
      // PHASE 1
      if (!(this_info.get_class_decl() == cd))
	errors.error(cd,cd,consym("class redeclared: ",name))
      else if (is_null(super_info.get_class_decl())) // force "extends Any()"
	class_table.lookup(any_sym).add_child(this_info)
      else {
	cd.set_superclass(super_info.get_class_decl());
	super_info.add_child(this_info)
      }
    } else if (!feature_tables_ready) {
      // PHASE 2
      if (parent == native_sym) null
      else if (parent == nothing_sym)
	errors.error(cd,cd,"cannot inherit from special type: 'Nothing'")
      else if (parent == null_sym)
	errors.error(cd,cd,"cannot inherit from special type: 'Null'")
      else if (parent == bool_sym)
	errors.error(cd,cd,"cannot inherit from special class: 'Boolean'")
      else if (parent == int_sym)
	errors.error(cd,cd,"cannot inherit from special class: 'Int'")
      else if (parent == unit_sym)
	errors.error(cd,cd,"cannot inherit from special class: 'Unit'")
      else if (is_null(super_info.get_class_decl())) {
	errors.error(cd,cd,consym("superclass undeclared: ",parent))
      } else
	if (!super_info.get_class_decl().get_inheritablep())
	  errors.error(cd,cd,
		       consym("cannot inherit from special class: ",parent))
        else null;
	this_info.check_feature_tables(root_methods,root_environment)
    } else 
    // @)
    {
      // @@ PHASE 3
      current_class = cd;
      current_env = this_info.environment(); // @@
      // TODO PA4/PA5: set current_env
      features.accept(this)
    }
  };
  
  var current_class : Cclass_decl = null;
  var current_env : Environment = null;

  def err(loc : CoolNode, message : String) : Unit =
    errors.error(current_class,loc,message);

  override def visit_Features_one(f : Feature) : Any = {
    f.set_owner(current_class); //@@
    //##PA5: TODO: set "owner" attribute
    f.accept(this)
  };

  override def visit_attr(the_node:Cattr,name:Symbol,of_type:Symbol) : Any = {
    // #(
    var of_class : Cclass_decl = class_table.lookup_class(of_type);
    if (of_type == nothing_sym) 
      err(the_node,"attributes may not be given type Nothing")
    else if (of_type == null_sym) ()
    else if (is_null(of_class)) 
      err(the_node,consym("class of attribute undeclared: ",of_type))
    else the_node.set_feature_of_class(of_class)
    // #)
    // PA4: TODO: check types, set attributes
  };

  override def visit_method(m:Cmethod,overridep:Boolean,name:Symbol,formals:Formals,return_type:Symbol,body:Expression) : Unit = {
    // #(
    table_env = new TableEnvironment(current_env);
    formals.accept(this);
    check_expr(body,table_env);
    var of_class : Cclass_decl = class_table.lookup_class(return_type);
    m.set_feature_of_class(of_class);
    if (is_null(of_class)) 
      if (return_type == nothing_sym) ()
      else if (return_type == null_sym) ()
      else err(m,consym("return type undeclared: ",return_type))
    else {};
    // PA5: check that overridden method (if any) is correctly overridden
    { // @(
      current_env.check_type_leq(body,"method body",
				 body.get_of_type(),return_type);
      var om : Cmethod = m.get_overrides();
      if (is_null(om)) ()
      else if (!current_env.type_leq(return_type,om.get_return_type()))
	current_env.err(m,"Return type in override not subtype")
      else if (!(formals.size() == om.get_formals().size()))
	current_env.err(m,"Number of formal parameters in override is wrong")
      else if (!formals_match(formals,om.get_formals()))
	current_env.err(m,"Formal parameters in override differ")
      else ()
    } // @)
    // #)
    // PA4: TODO: set up the current environment (with formals), check types
    //      check that body type checks, 
  };

  // #(
  // @(
  // only call this method with two sequences of equal length.
  def formals_match(fs1 : Formals, fs2 : Formals) : Boolean = {
    var all_match : Boolean = true;
    var e1 : FormalsEnumeration = fs1.elements();
    var e2 : FormalsEnumeration = fs2.elements();
    while (if (all_match) if (e1.hasNext()) e2.hasNext() else false else false){
      var f1 : Cformal = e1.next() match { case f:Cformal => f };
      var f2 : Cformal = e2.next() match { case f:Cformal => f };
      all_match = f1.get_of_type() == f2.get_of_type()
    };
    all_match
  };
  // @)

  var table_env : TableEnvironment = null;

  override def visit_Formals_one(f : Formal) : Any = f.accept(this);

  override def visit_formal(f:Cformal,name:Symbol,of_type:Symbol) : Any = {
    if (!is_null(table_env.probe(name))) 
      err(f,consym("redeclared formal ",name))
    else table_env.add(name,f);
    var of_class : Cclass_decl = class_table.lookup_class(of_type);
    if (of_type == nothing_sym) null
    else if (of_type == null_sym) null
    else if (is_null(of_class)) 
      err(f,consym("undeclared class: ",of_type))
    else f.set_formal_of_class(of_class)
  };

  var unit_sym : Symbol = io.symbol("Unit");
  var bool_sym : Symbol = io.symbol("Boolean");
  var int_sym : Symbol = io.symbol("Int");
  var string_sym : Symbol = io.symbol("String");
  var ignore_sym : Symbol = io.symbol("_ignore");
  var error_type : Symbol = nothing_sym;

  def check_expr(e : Expression, env : Environment) : Symbol = {
    // println("Checking " + e);
    e.set_of_type(e match {
      case n:Cno_expr => nothing_sym
	
      case v:Cvariable =>
	var vb : CoolNode = env.lookup(v.get_name());
        e.set_binding(vb);
        if (is_null(vb)) { 
	  err(v,consym("undeclared variable: ",v.get_name())); 
	  error_type 
	}
	else binding_type(vb)

      case a:Cassign =>
	var vtype : Symbol = any_sym;
        var name : Symbol = a.get_name();
        var b : CoolNode = env.lookup(a.get_name());
        if (is_null(b)) b = a.get_binding() else a.set_binding(b);
	b match {
	  case null =>
	    err(a,consym("undeclared variable in assignment ",name))
	  case b:Case =>
	    err(a,consym("cannot assign to branch variable ",name))
	  case t:Class =>
	    err(a,"cannot assign to 'this'")
	  case f:Formal =>
	    err(a,consym("cannot assign to formal ",name))
	  case vb:CoolNode =>
	    vtype = binding_type(vb)
	};
        env.check_type_leq(a,consym("assignment to ",name),
			   check_expr(a.get_expr(),env),vtype);
        unit_sym

      case d:Cdispatch =>
        check_exprs(d.get_actuals(),env);
	check_expr(d.get_expr(),env) match {
	  case null => nothing_sym
	  case s:Symbol => 
	    check_dispatch(d,s,d.get_name(),d.get_actuals())
	}

      case d:Cstatic_dispatch =>
        check_exprs(d.get_actuals(),env);
        if (is_null(class_table.lookup_class(d.get_type_name())))
          err(d,consym("Undeclared class: ",d.get_type_name())) // redundant
	else
        // The following check should never fail
          env.check_type_leq(d,"internal static dispatch",
		  	     check_expr(d.get_expr(),env),d.get_type_name());
        check_dispatch(d,d.get_type_name(),d.get_name(),d.get_actuals())

      case c:Ccond =>
	check_bool(c,"predicate of 'if'",c.get_pred(),env);
        env.type_lub(check_expr(c.get_then_exp(),env),
		     check_expr(c.get_else_exp(),env))

      case l:Cloop =>
	check_bool(l,"predicate of 'while'",l.get_pred(),env);
        check_expr(l.get_body(),env);
        unit_sym

      case c:Ctypecase =>
	check_expr(c.get_expr(),env);
        var vt : Symbol = c.get_expr().get_of_type();
        var cs : Cases = c.get_cases();
        var rt : Symbol = nothing_sym;
        var ei : CasesEnumeration = cs.elements();
        while (ei.hasNext()) {
	  ei.next() match {
	    case ci:Cbranch =>
	      var is : Symbol = ci.get_local_type();
	      if (is == null_sym) 
		if (symbol_name(ci.get_name()) == "null")
		  if (current_env.type_leq(is,vt)) ()
		  else err(ci, consym("Case not possible for ",vt).concat(": 'Null'"))
	        else err(ci,"'Null' cannot be explicitly checked for, use 'null'")
	      else if (is == nothing_sym) err(ci,"'Nothing' is not a legal case")
	      else class_table.lookup_class(is) match {
		case null => err(ci,consym("Undeclared case class: ",is))
		case cd:Cclass_decl => ci.set_case_of_class(cd);
		  if (current_env.type_leq(is,vt)) () else
		    if (current_env.type_leq(vt,is)) () else
		      err(ci,consym(consym("Case not possible for ",vt).concat(": "), is))
	      };
	      var done : Boolean = false;
              var ej : CasesEnumeration = cs.elements();
	      while (!done) {
                ej.next() match {
		  case cj:Cbranch =>
		    if (ci == cj) done = true
		    else if (if (is == null_sym) cj.get_local_type() == null_sym
			     else current_env.type_leq(is,cj.get_local_type()))
		      { err(ci,consym("Case already covered: ",is));
		        done = true }
		    else ()
		}
	      };
	      var newenv : Environment =
		new SingleEnvironment(ci.get_name(),ci,env);
	      var ty : Symbol = check_expr(ci.get_expr(),newenv);
	      ci.set_case_of_type(ty);
	      rt = env.type_lub(rt,ty)
	  }
	};
        rt

      case b:Cblock => 
	check_exprs(b.get_body(),env)

      case l:Clet =>
	var n : Symbol = l.get_identifier();
        var ty : Symbol = l.get_local_type();
        if (!is_null(env.lookup(n)))
	  err(l,consym("local shadows existing variable ",n))
	else null;
	class_table.lookup_class(ty) match {
	  case null =>
	    if (ty == null_sym) ()
	    else if (ty == nothing_sym) ()
	    else err(l,consym("type of local is undeclared: ",ty))
	  case cd:Cclass_decl => 
	    l.set_of_class(cd)
	};
        env.check_type_leq(l,consym("initialization of ",n),
			   check_expr(l.get_init(),env),ty);
        check_expr(l.get_body(),new SingleEnvironment(n,l,env))

      case op:Cadd =>
	check_binary(op,"+",op.get_e1(),op.get_e2(),env); int_sym

      case op:Csub =>
	check_binary(op,"-",op.get_e1(),op.get_e2(),env); int_sym

      case op:Cmul =>
	check_binary(op,"*",op.get_e1(),op.get_e2(),env); int_sym

      case op:Cdiv =>
	check_binary(op,"/",op.get_e1(),op.get_e2(),env); int_sym

      case op:Cneg =>
	check_int(op,"operand of '-'",op.get_e1(),env); int_sym

      case op:Clt =>
	check_binary(op,"<",op.get_e1(),op.get_e2(),env); bool_sym

      case op:Cleq =>
	check_binary(op,"<=",op.get_e1(),op.get_e2(),env); bool_sym

      case op:Ccomp =>
	check_bool(op,"operand of '!'",op.get_e1(),env); bool_sym

      case l:Cint_lit => int_sym
      case l:Cbool_lit => bool_sym
      case l:Cstring_lit => string_sym

      case a:Calloc =>
	var t : Symbol = a.get_type_name();
        if (t == bool_sym) err(a,"cannot instantiate value class Boolean")
        else if (t == int_sym) err(a,"cannot instantiate value class Int")
        else if (t == unit_sym) err(a,"cannot instantiate value class Unit")
        else if (t == any_sym) err(a,"cannot instantiate value class Any")
        else if (t == symbol_sym) err(a,"cannot instantiate value class Symbol")
	else class_table.lookup_class(t) match {
	  case null => 
	    err(a,consym("undeclared class for 'new': ",t))
	  case cd:Cclass_decl =>
	    a.set_of_class(cd)
	};
        t

      case u:Cunit => unit_sym
      case u:Cnil => null_sym
    });
    e.get_of_type()
  };

  var last_type : Symbol = null;
  def check_exprs(es : Expressions, env : Environment) : Symbol = {
    var saved : Environment = current_env;
    current_env = env;
    last_type = unit_sym;
    es.accept(this);
    current_env = saved;
    last_type
  };
  override def visit_Expressions_one(e : Expression) : Any =
    last_type = check_expr(e,current_env);
  
  def check_binary(op : CoolNode, name : String, e1 : Expression, e2 : Expression, env: Environment) : Unit = {
    check_int(op,"left operand of '".concat(name).concat("'"),e1,env);
    check_int(op,"right operand of '".concat(name).concat("'"),e2,env)
  };

  def check_int(n : CoolNode, desc : String, e:Expression, env:Environment) : Unit =
    if (! (check_expr(e,env) == int_sym))
      err(n,desc.concat(" must be 'Int'"))
    else ();

  def check_bool(n : CoolNode, desc : String, e:Expression, env:Environment) : Unit =
    if (!(check_expr(e,env) == bool_sym))
      err(n,desc.concat(" must be 'Boolean'"))
    else ();

  def binding_type(c : CoolNode) : Symbol =
    c match {
      case null => null
      case cd:Cclass_decl => cd.get_name()
      case a:Cattr => a.get_of_type()
      case f:Cformal => f.get_of_type()
      case l:Clet => l.get_local_type()
      case b:Cbranch => b.get_local_type()
    };

  def check_dispatch(e:Expression,tn:Symbol,mn:Symbol,es:Expressions) : Symbol={
    //@(
    class_table.lookup(tn).lookup_method(mn) match {
      case null =>
	if (tn == null_sym) err(e,consym("'Null' dispatch: ",mn))
	else if (tn == nothing_sym) err(e,consym("'Nothing' dispatch: ",mn))
	else err(e,consym("Undeclared method: ",mn))
      case m:Cmethod =>
	e.set_mbinding(m)
    };
    //@)
    var m : Cmethod = e.get_mbinding();
    if (!is_null(m)) {
      var fs : Formals = m.get_formals();
      var n : Int = fs.size();
      if (!(es.size() == n))
	err(e,"Wrong number of parameters (".concat(es.size().toString())
	    .concat(") to ").concat(mn.toString()).concat("', expected ")
	    .concat(n.toString()))
      else {
	var fe : FormalsEnumeration = fs.elements();
        var ee : ExpressionsEnumeration = es.elements();
	var i : Int = 0;
	while (fe.hasNext()) {
          i = i + 1;
	  fe.next() match {
	    case f:Cformal =>
	      current_env.check_type_leq(e,"parameter #".concat(i.toString()),
					 ee.next().get_of_type(),f.get_of_type())
	  }
	}
      };
      m.get_return_type()
    } else error_type
  };
  //#)
}


class SemantErrors(var options : CoolOptions) extends IO()
{
  var num_errors : Int = 0;

  def error(cd : Cclass_decl, loc : CoolNode, s: String) : Unit = 
    //@(
    if (!(options.get_strip_attributes() == 0)) () else
    //@)
  {
    if (options.get_semant_debug())
      out_any(loc)
    else {
      if (is_null(cd)) out("<unknown>") 
      else out(symbol_name(cd.get_filename()));
      out(":").out_any(loc.get_line_number())
    };
    out(": ").out(s).out("\n");
    num_errors = num_errors + 1
  };

  def has_errors() : Boolean = 0 < num_errors;
}


/**
 * This class represents a partially implemented interface
 * used with the DECORATOR
 * design pattern.  Please read up on this design pattern.
 */
class Environment() extends IO()
{
  def err(loc : CoolNode, message : String) : Unit = abort("abstract!");

  def error(cd : Cclass_decl, loc : CoolNode, message : String) : Unit =
    abort("abstract!");

  def lookup(key : Symbol) : CoolNode = abort("abstract");

  def type_leq(t1 : Symbol, t2 : Symbol) : Boolean = type_lub(t1,t2) == t2;

  def check_type_leq(n : CoolNode, s : String, t1 : Symbol, t2 : Symbol):Unit =
    if (!type_leq(t1,t2)) 
      err(n,"Type mismatch at ".concat(s)) 
    else ();

  def type_lub(t1 : Symbol, t2 : Symbol) : Symbol = abort("abstract!");
}

// #(
class RootEnvironment(var class_table : ClassTable, var errors : SemantErrors) 
extends Environment()
{
  override def lookup(key : Symbol) : CoolNode = null;
  override def error(cd : Cclass_decl, loc : CoolNode, message : String):Unit =
    errors.error(cd,loc,message);
  override def err(loc : CoolNode, message : String) : Unit =
    error(null,loc,message);

  var any_sym : Symbol = symbol("Any");
  var null_sym : Symbol = symbol("Null");
  var nothing_sym : Symbol = symbol("Nothing");
  var bool_sym : Symbol = symbol("Boolean");
  var int_sym : Symbol = symbol("Int");
  var unit_sym : Symbol = symbol("Unit");

  override def type_lub(t1 : Symbol, t2 : Symbol) : Symbol = {
    if (t1 == t2) t1
    else if (t1 == nothing_sym) t2
    else if (t2 == nothing_sym) t1
    else if (t1 == bool_sym) any_sym
    else if (t2 == bool_sym) any_sym
    else if (t1 == int_sym) any_sym
    else if (t2 == int_sym) any_sym
    else if (t1 == unit_sym) any_sym
    else if (t2 == unit_sym) any_sym
    else if (t1 == null_sym) t2
    else if (t2 == null_sym) t1
    else {
      // @(
      var i1 : ClassInfo = class_table.lookup(t1);
      var i2 : ClassInfo = class_table.lookup(t2);
      var diff : Int = i1.get_level() - i2.get_level();
      if (i1.get_level() == -1) any_sym
      else if (i2.get_level() == -1) any_sym
      else if (diff < 0) lub_helper(t1,supern(t2,-diff),i1.get_level())
      else lub_helper(supern(t1,diff),t2,i2.get_level())
      /* @)
      any_sym //!! Too coarse.  This is the PA4 solution
      @@ */
      // PA5: Use class info graph to compute lub.
    }
  };
  // @(

  def get_super(t : Symbol) : Symbol =
    class_table.lookup(t).get_class_decl().get_parent();

  def supern(t : Symbol, n : Int) : Symbol =
    if (n == 0) t else supern(get_super(t),n-1);

  def lub_helper(t1 : Symbol, t2 : Symbol, max : Int) : Symbol =
    if (t1 == t2) t1
    else if (max == 0) any_sym
    else lub_helper(get_super(t1),get_super(t2),max-1);
  // @)
}
// #)

/**
 * A abstract Decorator (q.v.) for a nested contour.
 * This class is extended by concrete decorator classes.
 * Compare to java.io.FilterOutputStream.
 */ 
class NestedEnvironment(var outer : Environment) extends Environment() 
{
  override def error(cd : Cclass_decl, loc : CoolNode, message : String):Unit =
    outer.error(cd,loc,message);

  override def err(loc : CoolNode, message : String) : Unit =
    outer.err(loc,message);

  override def lookup(key : Symbol) : CoolNode = outer.lookup(key);

  override def type_lub(t1 : Symbol, t2 : Symbol) : Symbol = 
    outer.type_lub(t1,t2);
}

// #(
class TableEnvironment (var outere : Environment) 
extends NestedEnvironment(outere)
{
  var table : Hashtable = new Hashtable();

  def probe(key : Symbol) : CoolNode = {
    table.get(key) match {
      case null => null
      case vb:CoolNode => vb
    }
  };

  override def lookup(key : Symbol) : CoolNode = {
    table.get(key) match {
      case null => super.lookup(key)
      case vb:CoolNode => vb
    }
  };

  def add(name : Symbol, vb : CoolNode) : Unit = {
    table.put(name,vb); ()
  };
}
// #)

/**
 * A concrete decorator for a contour with a single declaration.
 */
class SingleEnvironment (var name : Symbol, var node : CoolNode, var outere : Environment) 
extends NestedEnvironment(outere)
{
  override def lookup(key : Symbol) : CoolNode =
    if (key == name) node else super.lookup(key);
}

// #(
class ClassEnvironment(var class_decl : Cclass_decl, 
		       var superenv : Environment) 
extends TableEnvironment(superenv)
{
  { add(symbol("this"),class_decl) };

  override def err(loc : CoolNode, message : String) : Unit =
    superenv.error(class_decl,loc,message);
}
// #)
// PA4: Define new environment classes
//      The solution has three other environment classes.
//      Only two are used in the PA4 solution.

class ClassTable(var classes : Classes, var errors : SemantErrors) 
extends CoolVisitor() 
{
  var table : Hashtable = new Hashtable();

  { classes.accept(this) } ;

  override def visit_Classes_one(cl : Class) : Any = cl.accept(this);
  // #(
  override def visit_class_decl(n : Cclass_decl, name:Symbol,parent:Symbol,
		       features:Features,filename:Symbol) : Any =
    if (is_null(table.get(name)))
      table.put(name,new ClassDeclInfo(n,errors))
    else null;
  // #)
  // Use Visitor to insert every class into the table.
  // For PA4, the value can be the class_decl node itself
  // For PA5, you may want to put in a structure that
  //          can be used as a node in the inheritance graph.

  // #(
  var no_info : ClassInfo = new ClassInfo();

  def lookup(sym : Symbol) : ClassInfo = {
    if (is_null(sym)) no_info
    else table.get(sym) match {
      case null => no_info
      case ci:ClassInfo => ci
    }
  };

  def lookup_class(sym : Symbol) : Cclass_decl = lookup(sym).get_class_decl();

  def get_info(c:Class) : ClassInfo = {
    c match {
      case null => no_info
      case cd:Cclass_decl => lookup(cd.get_name())
    }
  };
  /* #)
  def lookup_class(sym : Symbol) : Cclass_decl = abort("TODO");
  ## */
}

// #(
class ClassInfo() extends IO()
{
  def get_class_decl() : Cclass_decl = null;
  //@(
  def get_level() : Int = -1;
  def add_child(ci : ClassInfo) : Unit = ();
  def set_sibling(ci : ClassInfo) : Unit = ();
  def build_feature_tables(level : Int,
                           super_methods : MethodTable, 
                           super_attrs : Environment) : Unit = ();
  def check_feature_tables(super_methods : MethodTable, 
                           super_attrs : Environment) : Unit = ();
  def lookup_method(name : Symbol) : Cmethod = null;
  def environment() : Environment = null;
  //@)
  // Add other "abstract" methods here.
}

class ClassDeclInfo(var class_decl : Cclass_decl, var errors : SemantErrors) 
extends ClassInfo() {
  override def get_class_decl() : Cclass_decl = class_decl;

  //@(
  // graph connections
  var level : Int = 0;
  var first_child_info : ClassInfo = new ClassInfo();
  var next_child_info : ClassInfo = first_child_info;

  override def get_level() : Int = level;

  override def add_child(ci: ClassInfo) : Unit = {
    ci.set_sibling(first_child_info);
    first_child_info = ci
  };
  override def set_sibling(ci : ClassInfo) : Unit = next_child_info = ci;
    
  var method_table : MethodTable = null;
  var attr_table : ClassEnvironment = null;

  override def build_feature_tables(defined_level : Int,
                                    super_methods : MethodTable, 
				    super_attrs : Environment) : Unit = {
    if (is_null(method_table)) {
      level = defined_level;
      next_child_info.build_feature_tables(level,super_methods,super_attrs);
      var features : Features = class_decl.get_features();
      method_table = new ClassMethodTable(class_decl,super_methods);
      attr_table = new ClassEnvironment(class_decl,super_attrs);
      features.accept(new FillFeatureTables(method_table,attr_table));
      first_child_info.build_feature_tables(level+1,method_table,attr_table)
    } else ()
  };

  override def check_feature_tables(super_methods : MethodTable, 
				    super_attrs : Environment) : Unit = {
    if (is_null(method_table)) {
      errors.error(class_decl,class_decl,
		   "Class ".concat(symbol_name(class_decl.get_name()))
		   .concat(" involved in cyclic inheritance"));
      build_feature_tables(0,super_methods,super_attrs)
    } else ()
  };

  override def lookup_method(name : Symbol) : Cmethod = 
    method_table.lookup(name);

  override def environment() : Environment = attr_table;
  //@)
}

//@(
class FillFeatureTables(var methods : MethodTable, var attrs : TableEnvironment)
extends CoolVisitor()
{
  def consym(s : String, sym : Symbol) : String =
    s.concat(sym.toString()).concat("'");

  override def visit_Features_one(node:Feature) : Any = node.accept(this);

  override def visit_method(m:Cmethod,o:Boolean,name:Symbol,fs:Formals,
                            rtype:Symbol,expr:Expression) : Any = {
    methods.probe(name) match {
      case null =>
	methods.lookup(name) match {
	  case null =>
	    if (o) attrs.err(m,consym("No method to override: ",name)) else null
	  case om:Cmethod =>
	    m.set_overrides(om);
	    if (!o) 
	      attrs.err(m,consym("Method should be 'override': ",name)) 
	    else null
	};
	methods.add(m)
      case om:Cmethod =>
	attrs.err(m,consym("Method redeclared: ",name))
    }
  };

  override def visit_attr(a:Cattr,name:Symbol,of_type:Symbol) : Any = {
    attrs.probe(name) match {
      case null =>
	attrs.lookup(name) match {
	  case null => attrs.add(name,a)
	  case oa:Cattr =>
	    attrs.err(a,consym("Attribute shadowing not allowed: ",name))
	}
      case oa:Cattr =>
	attrs.err(a,consym("Attribute redeclared: ",name))
    }
  };
}

class MethodTable() extends IO()
{
  def probe(mn : Symbol) : Cmethod = null;

  def lookup(mn : Symbol) : Cmethod = null;

  def add(m : Cmethod) : Unit = abort("can't add to null table");
}

class ClassMethodTable(var class_decl : Cclass_decl, var outer : MethodTable)
extends MethodTable()
{
  var table : Hashtable = new Hashtable();

  override def probe(mn : Symbol) : Cmethod =
    table.get(mn) match {
      case null => null
      case m:Cmethod => m
    };

  override def lookup(mn : Symbol) : Cmethod =
    table.get(mn) match {
      case null => outer.lookup(mn)
      case m:Cmethod => m
    };

  override def add(m : Cmethod) : Unit = { table.put(m.get_name(),m); ()};
}
//@)
// Many more helper classes for PA5:
//   - nodes for inheritance graph
//   - method tables
//   - helpers to create attr/method tables
//#)
class CodeGen(var program : Program, var options : CoolOptions, var output : IO)
extends CoolVisitor()
{
  def run() : Unit = {
    program.accept(this); ()
  };

  var emitter : Emitter = new Emitter(output,options.get_enable_gc());

  var code_info_table : CodeInfoTable = null;

  // #(
  var any_class_info : ClassCodeInfo = null;
  var int_class_info : ClassCodeInfo = null;
  var unit_class_info : ClassCodeInfo = null;
  var boolean_class_info : ClassCodeInfo = null;
  var string_class_info : ClassCodeInfo = null;

  var string_table : StringTable = null;
  var int_table : IntTable = null;

  var null_sym : Symbol = symbol("Null");

  // #)

  override def visit_program(the_node:Cprogram,classes:Classes) : Any = {
    code_info_table = new CodeInfoTable(options,classes);    
    // #(
    any_class_info = code_info_table.get_class_info(program.get_any_class());
    int_class_info = code_info_table.get_class_info(program.get_int_class());
    unit_class_info = code_info_table.get_class_info(program.get_unit_class());
    boolean_class_info =
      code_info_table.get_class_info(program.get_boolean_class());
    string_class_info =
      code_info_table.get_class_info(program.get_string_class());
    var empty : ArrayAny = new ArrayAny(0);
    any_class_info.set_tags(0,empty,empty);
    // #)
    // PA6: set offsets

    if (options.get_cgen_debug()) {
      new PrintCodeInfo(code_info_table).run(the_node)
    } else {};

    emit_boilerplate();
    
    // #(
    int_table = new IntTable(int_class_info.get_class_tag());
    string_table = new StringTable(string_class_info.get_class_tag(),int_table);
    program.accept(new FillLitTables(string_table,int_table));

    // emit all literals:
    var unit_tag : Int = unit_class_info.get_class_tag();
    emitter.obj_header(emitter.s_UNITLIT(),"Unit",unit_tag,0);
    var boolean_tag : Int = boolean_class_info.get_class_tag();
    emitter.obj_header(emitter.s_FALSE(),"Boolean",boolean_tag,1);
    emitter.word(0);
    emitter.obj_header(emitter.s_TRUE(),"Boolean",boolean_tag,1);
    emitter.word(1);
    int_table.emit(emitter);
    string_table.emit(emitter);

    // class name table: (ordered by class tag)
    emitter.label_def(emitter.s_CLASSNAMETAB());
    any_class_info.emit_classname_table(emitter,string_table);

    // all prototype objects and dispatch tables
    any_class_info.emit(emitter);
    // #)
    // PA6: control all the setting of tags, generation of
    // literals, generation of prototype objects, generation of 
    // class name table.

    // all methods
    emitter.text();
    classes.accept(this);

    // needed to make spim happy
    // For some reason, this can't be put in cool-runtime.s
    emitter.label_def("main");
    emitter.opc("jr").opn(emitter.s_RA()).endl(program);
    emitter.endl(program);

    emitter.data();
    emitter.global_def(emitter.s_HEAPSTART())
  };

  def emit_boilerplate() : Unit = {
    emitter.global(emitter.s_CLASSNAMETAB());
    emitter.global("Main".concat(emitter.s_PROTOBJ()));
    emitter.global("Int".concat(emitter.s_PROTOBJ()));
    emitter.global("Boolean".concat(emitter.s_PROTOBJ()));
    emitter.global("String".concat(emitter.s_PROTOBJ()));
    emitter.global("Symbol".concat(emitter.s_PROTOBJ()));
    emitter.global(emitter.s_UNITLIT());
    emitter.global(emitter.s_FALSE());
    emitter.global(emitter.s_TRUE());
    ()
  };

  override def visit_Classes_one(node:Class) : Any = node.accept(this);
  override def visit_class_decl(cd:Cclass_decl,name:Symbol,parent:Symbol,
                                features:Features,filename:Symbol) : Any = {
    current_class = cd;
    features.accept(this)
  };
  
  var current_class : Cclass_decl = null;

  override def visit_Features_one(f : Feature) : Any = f.accept(this);

  override def visit_attr(n:Cattr,name:Symbol,of_type:Symbol) : Any = null;

  var formal_offset : Int = 0; // ## @@

  override def visit_method(the_node:Cmethod,overridep:Boolean,name:Symbol,formals:Formals,return_type:Symbol,body:Expression) : Any = {
    //#(
    // @(
    var temp_calc : TempCalculator = new TempCalculator(code_info_table);
    temp_calc.calc(body,0);
    var max_offset : Int = temp_calc.get_max();
    // println("Method " + name + " has " + max_offset + " temps.");
    formal_offset = max_offset + 3 + formals.size();
    formals.accept(this);
    body match {
      case x:Cno_expr => 	// native code
      case e:Expression =>
	emitter.label_def(emitter.s_METHOD(current_class.get_name(),name));
        gen_method_body(formals,e,max_offset)
    }
    // @)
    // PA7: compute number of temps needs
    // Assign offsets to formals
    // If not native (no_expr),
    //   (1) emit prologue
    //   (2) generate code for body
    //   (3) emit epilogue
    //#)
  };

  // #(
  // @(
  def gen_method_body(formals : Formals, e : Expression, max : Int) : Any = {
    emitter.prologue(max);
    code(e);
    emitter.epilogue(max,formals.size())
  };

  override def visit_Formals_one(f : Formal) : Any = {
    formal_offset = formal_offset - 1;
    code_info_table.set_info(f,formal_offset)
  };

  var last_label : Int = 0;
  def gen_label() : String = {
    last_label = last_label+1;
    "L".concat(last_label.toString())
  };

  def gen_temp(offset : Int) : String =
    emitter.gen_offset(emitter.s_FP(),offset);
    
  def gen_binding(binding : CoolNode) : String = binding match {
    case cd:Cclass_decl => "$s0"
    case a:Cattr => 
      emitter.gen_offset(emitter.s_SELF(),
			 emitter.i_ATTROFFSET()+
			 code_info_table.get_offset_info(a))
    case n:CoolNode => 
      gen_temp(code_info_table.get_offset_info(n))
  };
      
  var acc : String = emitter.s_ACC();
  var t1 : String = emitter.s_T1();
  var t2 : String = emitter.s_T2();

  var this_sym : Symbol = symbol("this");

  def code(e : Expression) : Any = {
    e match {
      case n:Cno_expr => abort("no_expr shouldn't be called!")
	
      case v:Cvariable =>
	if (v.get_name() == this_sym)
	  emitter.opc("move").opn(acc).opn(emitter.s_SELF()).endl(e)
	else
	  emitter.opc("lw").opn(acc)
                 .opn(gen_binding(e.get_binding())).endl(e)
      case a:Cassign =>
        code(a.get_expr());
	emitter.opc("sw").opn(acc)
               .opn(gen_binding(e.get_binding())).endl(e);
        if (options.get_enable_gc()) {
          e.get_binding() match {
	    case at:Cattr =>
	      emitter.gc_assign(code_info_table.get_offset_info(at))
	    case x:CoolNode =>
	  }
	} else ();
        code(new Cunit())

      case d:Cdispatch =>
	var m : Cmethod = d.get_mbinding();
        var toff : Int = code_info_table.get_offset_info(d);
        code_spill_expr(d.get_expr(),toff);
        code_actuals(d.get_actuals());
        code_unspill(d,toff,acc);
        var label : String = gen_label();
        emitter.opc("bnez").opn(acc).opn(label).endl(e);
        emitter.error_abort(emitter.s_DISPATCHABORT(),
			    string_table.get(current_class.get_filename()),
			    d.get_line_number());
        emitter.label_def(label);
        emitter.opc("lw").opn(t1)
               .offset(acc,emitter.i_DISPTABOFFSET()).endl(e);
        emitter.opc("lw").opn(t1)
               .offset(t1,code_info_table.get_offset_info(m)).endl(e);
        emitter.opc("jalr").opn(t1).endl(e)

      case d:Cstatic_dispatch =>
	var m : Cmethod = d.get_mbinding();
        var cd : Cclass_decl = m.get_owner();
        var mn : String = emitter.s_METHOD(cd.get_name(),m.get_name());
        var toff : Int = code_info_table.get_offset_info(d);
        code_spill_expr(d.get_expr(),toff);
        code_actuals(d.get_actuals());
        code_unspill(d,toff,acc);
        emitter.opc("jal").opn(mn).endl(e)

      case c:Ccond =>
        var else_label : String = gen_label();
        var done_label : String = gen_label();
        code(c.get_pred());
        emitter.opc("lw").opn(t1).offset(acc,emitter.i_ATTROFFSET()).endl(e);
        emitter.opc("beqz").opn(t1).opn(else_label).endl(e);
        code(c.get_then_exp());
        emitter.opc("b").opn(done_label).endl(e);
        emitter.label_def(else_label);
        code(c.get_else_exp());
        emitter.label_def(done_label)

      case l:Cloop =>
        var body_label : String = gen_label();
	var pred_label : String = gen_label();
        emitter.opc("b").opn(pred_label).endl(e);
        emitter.label_def(body_label);
        code(l.get_body());
        emitter.label_def(pred_label);
        code(l.get_pred());
        emitter.opc("lw").opn(t1).offset(acc,emitter.i_ATTROFFSET()).endl(e);
        emitter.opc("bnez").opn(t1).opn(body_label).endl(e);
        code(new Cunit())

      case c:Ctypecase =>
	var temp : String = code_spill_expr(c.get_expr(),code_info_table.get_offset_info(c));
        var error_label : String = gen_label();
        var done_label : String = gen_label();
        var nb : Cbranch = null;
        var cit : CasesEnumeration = c.get_cases().elements();
        while (cit.hasNext()) {
	  cit.next() match {
	    case b:Cbranch => 
	      if (b.get_local_type() == null_sym) nb = b else ()
	  }
	};  
        emitter.out("# typecase reg = ").out(temp).out("\n");
        if (is_null(nb)) {
	  emitter.opc("beqz").opn(temp).opn(error_label).endl(e)
	} else {
	  var nonnull_label : String = gen_label();
	  emitter.opc("bnez").opn(temp).opn(nonnull_label).endl(e);
	  code(nb.get_expr());
	  emitter.opc("b").opn(done_label).endl(nb);
	  emitter.label_def(nonnull_label)
	};
        emitter.opc("lw").opn(t1).offset(temp,emitter.i_TAGOFFSET()).endl(e);
        cit = c.get_cases().elements();
        while (cit.hasNext()) { 
	  cit.next() match {
	    case b : Cbranch => if (b == nb) () else {
	      var next_label : String = gen_label();
	      var cci : ClassCodeInfo = 
		code_info_table.get_class_info(b.get_case_of_class());
	      emitter.opc("blt").opn(t1).opn(cci.get_class_tag().toString())
              .opn(next_label).endl(b);
	      emitter.opc("bgt").opn(t1).opn(cci.get_max_tag().toString())
              .opn(next_label).endl(b);
	      code(b.get_expr());
	      emitter.opc("b").opn(done_label).endl(b);
	      emitter.label_def(next_label)
	    }
	  }
	};
        emitter.label_def(error_label);
        emitter.error_abort(emitter.s_CASEABORT(),
			    string_table.get(current_class.get_filename()),
			    c.get_line_number());
        emitter.label_def(done_label)

      case b:Cblock =>
	if (b.get_body().size() == 0)
	  code(new Cunit())
	else
	  code_exprs(b.get_body())

      case l:Clet =>
        var off : Int = code_info_table.get_offset_info(l);
        if (l.get_identifier() == this_sym) { // handle inlining optimization
	  code(l.get_init());
	  var temp : String = gen_temp(off);
	  emitter.opc("sw").opn(emitter.s_SELF()).opn(temp).endl(e);
	  emitter.opc("move").opn(emitter.s_SELF()).opn(acc).endl(e);
          code(l.get_body());
	  emitter.opc("lw").opn(emitter.s_SELF()).opn(temp).endl(e)
	} else {
	  code_spill_expr(l.get_init(),off);
          code(l.get_body())
	}

      case op:Cadd =>
	code_binary(op,op.get_e1(),op.get_e2(),true);
        emitter.opc("add").opn(t1).opn(t1).opn(t2).endl(e);
        emitter.opc("sw").opn(t1).offset(acc,emitter.i_ATTROFFSET()).endl(e)

      case op:Csub =>
	code_binary(op,op.get_e1(),op.get_e2(),true);
        emitter.opc("sub").opn(t1).opn(t1).opn(t2).endl(e);
        emitter.opc("sw").opn(t1).offset(acc,emitter.i_ATTROFFSET()).endl(e)

      case op:Cmul =>
	code_binary(op,op.get_e1(),op.get_e2(),true);
        emitter.opc("mulo").opn(t1).opn(t1).opn(t2).endl(e);
        emitter.opc("sw").opn(t1).offset(acc,emitter.i_ATTROFFSET()).endl(e)

      case op:Cdiv =>
	code_binary(op,op.get_e1(),op.get_e2(),true);
        var labok : String = gen_label();
        var labbad: String = gen_label();
        emitter.opc("beqz").opn(t2).opn(labbad).endl(e);
        emitter.opc("bne").opn(t2).opn("-1").opn(labok).endl(e);
        emitter.opc("bne").opn(t1).opn("0x80000000").opn(labok).endl(e);
        emitter.label_def(labbad);
        emitter.error_abort(emitter.s_DIVABORT(),
			    string_table.get(current_class.get_filename()),
			    e.get_line_number());
        emitter.label_def(labok);
        emitter.opc("div").opn(t1).opn(t1).opn(t2).endl(e);
        emitter.opc("sw").opn(t1).offset(acc,emitter.i_ATTROFFSET()).endl(e)

      case op:Cneg =>
	code(op.get_e1());
        emitter.opc("jal").opn(emitter.s_ANYCLONE()).endl(e);
        emitter.opc("lw").opn(t1).offset(acc,emitter.i_ATTROFFSET()).endl(e);
        emitter.opc("neg").opn(t1).opn(t1).endl(e);
        emitter.opc("sw").opn(t1).offset(acc,emitter.i_ATTROFFSET()).endl(e)

      case op:Clt =>
	code_binary(op,op.get_e1(),op.get_e2(),false);
        var done_label : String = gen_label();
        emitter.opc("la").opn(acc).opn(emitter.s_TRUE()).endl(e);
        emitter.opc("blt").opn(t1).opn(t2).opn(done_label).endl(e);
        emitter.opc("la").opn(acc).opn(emitter.s_FALSE()).endl(e);
        emitter.label_def(done_label)

      case op:Cleq =>
	code_binary(op,op.get_e1(),op.get_e2(),false);
        var done_label : String = gen_label();
        emitter.opc("la").opn(acc).opn(emitter.s_TRUE()).endl(e);
        emitter.opc("ble").opn(t1).opn(t2).opn(done_label).endl(e);
        emitter.opc("la").opn(acc).opn(emitter.s_FALSE()).endl(e);
        emitter.label_def(done_label)

      case op:Ccomp =>
	code(op.get_e1());
        emitter.opc("lw").opn(t1).offset(acc,emitter.i_ATTROFFSET()).endl(e);
        var done_label : String = gen_label();
        emitter.opc("la").opn(acc).opn(emitter.s_TRUE()).endl(e);
        emitter.opc("beqz").opn(t1).opn(done_label).endl(e);
        emitter.opc("la").opn(acc).opn(emitter.s_FALSE()).endl(e);
        emitter.label_def(done_label)

      case l:Cint_lit =>
	var il : String = emitter.s_INTLIT(int_table.get(l.get_token()));
	emitter.opc("la").opn(acc).opn(il).endl(e)

      case l:Cbool_lit =>
	var bl : String = emitter.s_BOOLEANLIT(l.get_value());
	emitter.opc("la").opn(acc).opn(bl).endl(e)

      case l:Cstring_lit =>
        var sl : String = emitter.s_STRINGLIT(string_table.get(l.get_token()));
        emitter.opc("la").opn(acc).opn(sl).endl(e)

      case a:Calloc =>
        var cs : String = symbol_name(a.get_type_name());
	var pl : String = cs.concat(emitter.s_PROTOBJ());
	emitter.opc("la").opn(acc).opn(pl).endl(e);
        emitter.opc("jal").opn(emitter.s_ANYCLONE()).endl(e)
      
      case u:Cunit => 
	emitter.opc("la").opn(acc).opn(emitter.s_UNITLIT()).endl(e)

      case u:Cnil => 
	emitter.opc("li").opn(acc).opn("0").endl(e)
    }
  };

  def code_spill_expr(e : Expression, toff : Int) : String = {
    code(e);
    var temp : String = gen_temp(toff);
    emitter.opc("sw").opn(acc).opn(temp).endl(e);
    acc
  };

  def code_unspill(e : CoolNode, toff : Int, reg : String) : Any = {
    var temp : String = gen_temp(toff);
    emitter.opc("lw").opn(reg).opn(temp).endl(e)
  };

  var is_actual : Boolean = false;
  
  def code_actuals(es : Expressions) : Unit = {
    var saved : Boolean = is_actual;
    is_actual = true;
    es.accept(this);
    is_actual = saved
  };

  def code_exprs(es : Expressions) : Unit = {
    var saved : Boolean = is_actual;
    is_actual = false;
    es.accept(this);
    is_actual = saved
  };
    
  override def visit_Expressions_one(e : Expression) : Any = {
    code(e);
    var sp : String = emitter.s_SP();
    if (is_actual) {
      emitter.opc("sw").opn(acc).offset(sp,0).endl(e);
      emitter.opc("addiu").opn(sp).opn(sp).opn("-4").endl(e)
    } else null
  };
  
  def code_binary(op : CoolNode, e1 : Expression, e2 : Expression, copy : Boolean) : Unit = {
    var toff : Int = code_info_table.get_offset_info(op);
    code_spill_expr(e1,toff);
    code(e2);
    if (copy) emitter.opc("jal").opn(emitter.s_ANYCLONE()).endl(op) else null;
    code_unspill(op,toff,t1);
    emitter.opc("lw").opn(t1).offset(t1,emitter.i_ATTROFFSET()).endl(op);
    emitter.opc("lw").opn(t2).offset(acc,emitter.i_ATTROFFSET()).endl(op);
    ()
  };

  def binding_type(c : CoolNode) : Symbol =
    c match {
      case null => null
      case cd:Cclass_decl => cd.get_name()
      case a:Cattr => a.get_of_type()
      case f:Cformal => f.get_of_type()
      case l:Clet => l.get_local_type()
      case b:Cbranch => b.get_local_type()
    };
  // @)
  // #)
  //## PA7: lots of helper methods
}


/** A class to handle formatting the assembly file.
 */
class Emitter(var output : IO, var enable_gc : Boolean) extends IO()
{
  // { new IO().out("enable_gc = ").out_any(enable_gc).out("\n") };
  override def out(s : String) : IO = output.out(s);

  // conventions
  def s_CLASSNAMETAB() : String = "class_nameTab";
  def s_CLASSOBJTAB() : String = "class_objTab";
  def s_HEAPSTART() : String = "heap_start";
  def s_DISPTAB() : String = "_dispTab";
  def s_PROTOBJ() : String = "_protObj";
  def s_METHODSEP() : String = ".";
  def s_ANYCLONE() : String = "Any.clone";
  def s_ERRORABORT() : String = "_error_abort";

  def s_METHOD(cn : Symbol, mn : Symbol) : String =
    symbol_name(cn).concat(s_METHODSEP()).concat(symbol_name(mn));
  
  def s_INTLIT(offset : Int) : String = 
    "int_lit".concat(offset.toString());
  def s_STRINGLIT(offset : Int) : String = 
    "string_lit".concat(offset.toString());
  def s_BOOLEANLIT(value : Boolean) : String =
    if (value) "boolean_lit1" else "boolean_lit0";
  def s_UNITLIT() : String = "unit_lit";

  def s_FALSE() : String = s_BOOLEANLIT(false);
  def s_TRUE() : String = s_BOOLEANLIT(true);

  def s_DISPATCHABORT() : String = "_dispatch_abort";
  def s_DIVABORT() : String = "_divide_abort";
  def s_CASEABORT() : String = "_case_abort";

  def i_WORDSIZE() : Int = 4;
  def i_TAGOFFSET() : Int = 0;
  def i_SIZEOFFSET() : Int = 1;
  def i_DISPTABOFFSET() : Int = 2;
  def i_ATTROFFSET() : Int = 3;
  def i_METHODOFFSET() : Int = 0;

  def s_ZERO() : String = "$zero";
  def s_ACC() : String = "$a0";
  def s_AUX() : String = "$a1"; // for some primitive functions
  def s_SELF() : String = "$s0";
  def s_T1() : String = "$t1";
  def s_T2() : String = "$t2";
  def s_T3() : String = "$t3";
  def s_SP() : String = "$sp";
  def s_FP() : String = "$fp";
  def s_RA() : String = "$ra";

  { out("\t.data\n") };
  var mode : Int = 1; // 0 = text, 1 = data, 2 = in ascii

  def gen_offset(s : String, o : Int) : String =
    (o*i_WORDSIZE()).toString().concat("(").concat(s).concat(")");

  def opc(s : String) : Emitter = {out("\t").out(s).out("\t");this};
  def opn(s : String) : Emitter = {out(" ").out(s); this};
  def offset(s : String, o : Int) : Emitter = opn(gen_offset(s,o));

  var last_line : Int = 0;
  def endl(n : CoolNode) : Unit = {
    var l : Int = n.get_line_number();
    if (l == last_line) ()
    else if (l == 0) ()
    else { out("\t# line ").out_any(l); last_line = l };
    out("\n"); ()
  };

  def set_mode(n : Int) : Unit = {
    while (!(mode == n)) {
      if (mode == 2) {
	out("\"\n");
	mode = 1
      } else if (mode == 0) {
	out("\t.data\n");
	mode = 1
      } else if (n == 0) {
	out("\t.text\n");
	mode = 0
      } else {
	opc(".ascii").out("\"");
	mode = 2
      }
    }
  };

  def text() : Unit = set_mode(0);
  def data() : Unit = set_mode(1);
  def ascii() : Unit = set_mode(2);

  def char(ch : String) : Unit = {
    ascii();
    out(ch);
    ()
  };

  def byte(i : Int) : Unit = {
    data();
    opc(".byte").out_any(i).out("\n");
    ()
  };

  def align() : Unit = { 
    data(); 
    opc(".align").out_any(2).out("\n"); 
    ()
  };

  def global(name : String) : Any = opc(".globl").out(name).out("\n");
  def label_def(name : String) : Any = out(name).out(":\n");
  def global_def(name : String) : Any = { global(name); label_def(name) };

  def word(x : Any) : Any = out("\t.word\t").out(x.toString()).out("\n");

  {
    data();
    global_def("_MemMgr_INITIALIZER");
    word(if (enable_gc) "_GenGC_Init" else "_NoGC_Init");
    global_def("_MemMgr_COLLECTOR");
    word(if (enable_gc) "_GenGC_Collect" else "_NoGC_Collect");
    global_def("_MemMgr_TEST");
    word(0)
  };

  /** Generate code to record file and line numebr and then jump
   * to the appropriate error reporting routine in the runtime.
   */
  // An example of a helper method.  
  // The solution uses this whenever it needs to handle an "abort"
  def error_abort(target: String, fi : Int, li : Int) : Unit = {
    opc("la").opn(s_AUX()).opn(s_STRINGLIT(fi)).out("\n");
    opc("li").opn(s_T1()).opn(li.toString()).out("\n");
    opc("j").opn(target).out("\n");
    ()
  };

  // CS 654 students don't need to call this method
  // Only use if garbage collection is enabled.
  def gc_assign(offset : Int) : Unit = {
    opc("la").opn(s_AUX()).offset(s_SELF(),offset+i_ATTROFFSET()).out("\n");
    opc("jal").opn("_GenGC_Assign").out("\n");
    ()
  };

  // #(
  def obj_header(label : String, cn : String, tag : Int, size : Int) : Unit = {
    data();
    word(-1);
    label_def(label);
    word(tag);
    word(size+i_ATTROFFSET());
    word(cn.concat(s_DISPTAB()));
    ()
  };
  // #)
  // PA6: The solution defines a method for generating an object header

  //@(
  def prologue(temps : Int) : Unit = {
    opc("addiu").opn(s_SP()).opn(s_SP())
                .opn(((-3-temps)*i_WORDSIZE()).toString()).out("\n");
    opc("sw").opn(s_FP()).offset(s_SP(),temps+3).out("\n");
    opc("sw").opn(s_SELF()).offset(s_SP(),temps+2).out("\n");
    opc("sw").opn(s_RA()).offset(s_SP(),temps+1).out("\n");
    opc("addiu").opn(s_FP()).opn(s_SP())
                .opn(i_WORDSIZE().toString()).out("\n");
    opc("move").opn(s_SELF()).opn(s_ACC()).out("\n");
    if (enable_gc) {
      var i : Int = 0;
      while (i < temps) {
	opc("sw").opn(s_ZERO()).offset(s_FP(),i).out("\n");
	i = i + 1
      }
    } else ()
  };

  def epilogue(temps : Int, formals : Int) : Unit = {
    opc("lw").opn(s_FP()).offset(s_SP(),temps+3).out("\n");
    opc("lw").opn(s_SELF()).offset(s_SP(),temps+2).out("\n");
    opc("lw").opn(s_RA()).offset(s_SP(),temps+1).out("\n");
    opc("addiu").opn(s_SP()).opn(s_SP())
                .opn(((3+temps+formals)*i_WORDSIZE()).toString()).out("\n");
    opc("jr").opn(s_RA()).out("\n");
    ()
  };
  // @)
  //## PA7: The solution defines methods to generate prologue and epilogue
}

class CodeInfoTable(var options : CoolOptions, var classes : Classes) 
extends CoolVisitor()
{
  var table : ArrayAny = new ArrayAny(100);
  
  def get_raw_info(n : CoolNode) : Any =
    if (table.length() <= n.get_id()) null else table.get(n.get_id());

  def set_info(n : CoolNode, v : Any) : Unit = {
    while (table.length() <= n.get_id()) table = table.resize(table.length()*2);
    table.set(n.get_id(),v); ()
  };

  def get_offset_info(n : CoolNode) : Int =
    get_raw_info(n) match { case i:Int => i };

  // #(
  def get_class_info(n : Class) : ClassCodeInfo =
    n match {
      case null => null
      case cd:Cclass_decl =>
	get_raw_info(n) match { 
	  case null => 
	    var ci : ClassCodeInfo = new ClassCodeInfo(cd,this);
	    set_info(n,ci); ci
	  case ci:ClassCodeInfo => ci 
	}
    };

  def get_class_tag(n : Class) : Int = get_class_info(n).get_class_tag();

  { 
    classes.accept(this)
  };

  override def visit_Classes_one(node:Class) : Any = {
    var ci : ClassCodeInfo = get_class_info(node);
    var si : ClassCodeInfo = get_class_info(node.get_superclass());
    if (is_null(si)) null
    else si.add_child(ci)
  };
  // #) 
  // TODO
  // def get_class_tag(node:Class) : Int = ...

}

class PrintCodeInfo(var code_info_table : CodeInfoTable) extends CoolTreeVisitor() {
  def run(p : Program) : Any = {
    p.accept(this)
  };

  override def visit_class_decl(the_node:Cclass_decl,name:Symbol,parent:Symbol,features:Features,filename:Symbol) : Any = {
    out("class tag for ").out(symbol_name(name)).out(" = ");
    out_any(code_info_table.get_class_tag(the_node));
    out("\n");
    super.visit_class_decl(the_node,name,parent,features,filename)
  };

  override def visit_method(m:Cmethod,o:Boolean,name:Symbol,fs:Formals,
                            rtype:Symbol,expr:Expression) : Any = {
    out("  method tag for ").out(symbol_name(name)).out(" = ");
    out_any(code_info_table.get_offset_info(m));
    out("\n");
    super.visit_method(m,o,name,fs,rtype,expr)
  };

  override def visit_attr(a:Cattr,name:Symbol,of_type:Symbol) : Any = {
    out("  attr tag for ").out(symbol_name(name)).out(" = ");
    out_any(code_info_table.get_offset_info(a));
    out("\n");
    super.visit_attr(a,name,of_type)
  };
}

// #(
class ClassCodeInfo(var class_decl : Cclass_decl, var table : CodeInfoTable) 
extends CoolVisitor()
{
  def get_class_decl() : Cclass_decl = class_decl;

  // graph connections
  var first_child : ClassCodeInfo = null;
  var next_sibling : ClassCodeInfo = null;

  var class_tag : Int = 0;
  var max_class_tag : Int = 0;

  def get_class_tag() : Int = class_tag;
  def get_max_tag() : Int = max_class_tag;
  def get_sibling() : ClassCodeInfo = next_sibling;

  def add_child(ci: ClassCodeInfo) : Unit = {
    ci.set_sibling(first_child);
    first_child = ci
  };
  def set_sibling(ci : ClassCodeInfo) : Unit = next_sibling = ci;
    
  //@(
  def reverse_children() : Unit = {
    var old_children : ClassCodeInfo = first_child;
    var new_children : ClassCodeInfo = null;
    while (!is_null(old_children)) {
      var t : ClassCodeInfo = old_children;
      old_children = old_children.get_sibling();
      t.set_sibling(new_children);
      new_children = t
    };
    first_child = new_children
  };

  //@)
  var next_method : Int = 0;
  var next_attr : Int = 0;

  var method_array : ArrayAny = null;
  var attr_array : ArrayAny = null;

  def set_tags(ct : Int, methods : ArrayAny, attrs : ArrayAny) : Int = {
    class_tag = ct;
    next_method = methods.length();
    next_attr = attrs.length();
    class_decl.get_features().accept(this); // PHASE 1
    method_array = methods.resize(next_method);
    attr_array = attrs.resize(next_attr);
    class_decl.get_features().accept(this); // PHASE 2
    if (!is_null(first_child))
      max_class_tag = first_child.set_tags(ct+1,method_array,attr_array)
    else max_class_tag = ct;
    if (!is_null(next_sibling)) 
      next_sibling.set_tags(max_class_tag+1,methods,attrs)
    else max_class_tag
  };

  override def visit_Features_one(node:Feature) : Any = node.accept(this);

  override def visit_method(m:Cmethod,o:Boolean,name:Symbol,fs:Formals,
                            rtype:Symbol,expr:Expression) : Any = {
    if (!is_null(method_array))
      method_array.set(table.get_offset_info(m),m)
    else if (o) 
      table.set_info(m,table.get_offset_info(m.get_overrides()))
    else {
      table.set_info(m,next_method);
      next_method = next_method+1
    }
  };

  override def visit_attr(a:Cattr,name:Symbol,of_type:Symbol) : Any = {
    if (!is_null(attr_array))
      attr_array.set(table.get_offset_info(a),a)
    else {
      table.set_info(a,next_attr);
      next_attr = next_attr + 1
    }
  };

  var int_sym : Symbol = symbol("Int");
  var unit_sym : Symbol = symbol("Unit");
  var boolean_sym : Symbol = symbol("Boolean");

  def emit_classname_table(e : Emitter, st : StringTable) : Unit = {
    e.word(e.s_STRINGLIT(st.get(class_decl.get_name())));
    if (!is_null(first_child)) first_child.emit_classname_table(e,st)
    else ();
    if (!is_null(next_sibling)) next_sibling.emit_classname_table(e,st)
    else ()
  };
    
  def emit(e : Emitter) : Unit = {
    e.data();
    var cn : String = symbol_name(class_decl.get_name());
    var i : Int = 0;
    var n : Int = 0;
    e.label_def(cn.concat(e.s_DISPTAB()));
    i = 0; n = method_array.length();
    while (i < n) {
      var m : Cmethod = method_array.get(i) match { case m:Cmethod => m };
      var o : Cclass_decl = m.get_owner();
      e.word(e.s_METHOD(o.get_name(),m.get_name()));
      i = i + 1
    };
    if (!class_decl.get_inheritablep()) {
      e.global(cn.concat(e.s_PROTOBJ()))
    } else {};
    e.obj_header(cn.concat(e.s_PROTOBJ()),cn,class_tag,next_attr);
    i = 0; n = attr_array.length();
    while (i < n) {
      var a : Cattr = attr_array.get(i) match { case a:Cattr => a };
      var t : Symbol = a.get_of_type();
      if (t == int_sym) {
	e.word(e.s_INTLIT(0))
      } else if (t == boolean_sym) {
	e.word(e.s_FALSE())
      } else if (t == unit_sym) {
        e.word(e.s_UNITLIT())
      } else {
	e.word(0)
      };
      i = i + 1
    };
    if (!is_null(first_child)) first_child.emit(e) else ();
    if (!is_null(next_sibling)) next_sibling.emit(e) else ()
  };
}


class SymbolIntTable() extends IO()
{
  var table : Hashtable = new Hashtable();
  var next : Int = 0;

  def add(sym : Symbol) : Unit =
    table.get(sym) match {
      case null => table.put(sym,next); next = next + 1
      case i:Int => ()
    };

  def get(sym : Symbol) : Int =
    table.get(sym) match {
      case i:Int => i
    };

  def emit_one(e : Emitter, k : Symbol, i : Int) : Any = abort("abstract!");

  def emit(e : Emitter) : Unit = {
    e.data();
    var enum : Enumeration = table.elements();
    while (enum.hasNext()) {
      var p : Pair = enum.next() match { case p:Pair => p };
      var k : Symbol = p.first() match { case s:Symbol => s };
      var i : Int = p.second() match { case i:Int => i };
      emit_one(e,k,i)
    }
  };
}

class IntTable(var tag : Int) extends SymbolIntTable()
{
  def add_int(i : Int) : Unit = add(symbol(i.toString()));

  def get_int(i : Int) : Int = get(symbol(i.toString()));

  override def emit_one(e : Emitter, k : Symbol, i : Int) : Unit = {
    e.obj_header(e.s_INTLIT(i),"Int",tag,1);
    e.word(symbol_name(k));
    ()
  };

  { add_int(0) }; // force 0 to have index 0
}

class StringTable(var tag : Int, var it : IntTable) extends SymbolIntTable()
{
  override def add(sym : Symbol) : Unit = {
    super.add(sym);
    it.add_int(symbol_name(sym).length())
  };

  def add_string(s : String) : Unit = add(symbol(s));

  var first_printable : Int = 32;
  var last_printable : Int = 126;
  var quote : Int = "\"".charAt(0);
  var backslash : Int = "\\".charAt(0);

  override def emit_one(e : Emitter, k : Symbol, l : Int) : Unit = {
    var s : String = symbol_name(k);
    var n : Int = s.length();
    var sz : Int = (n + e.i_WORDSIZE())/e.i_WORDSIZE();

    e.obj_header(e.s_STRINGLIT(l),"String",tag,sz+1);
    e.word(e.s_INTLIT(it.get_int(n)));

    var i : Int = 0;
    while (i < n) {
      var ch : Int = s.charAt(i);
      if (if (ch < first_printable) false
	  else if (last_printable < ch) false
	  else if (ch == quote) false
	  else if (ch == backslash) false
	  else true) {
	e.ascii();
	e.out(s.substring(i,i+1))
      } else {
	e.byte(ch)
      };
      i = i + 1
    };
    e.byte(0);
    e.align()
  };

  { add_string("") }; // force "" to be string_lit 0
}

class FillLitTables(var st : StringTable, var it : IntTable)
extends CoolTreeVisitor()
{
  override def visit_class_decl(the_node:Cclass_decl,name:Symbol,parent:Symbol,features:Features,filename:Symbol) : Any = {
    st.add(name);
    st.add(filename);
    super.visit_class_decl(the_node,name,parent,features,filename)
  };

  override def visit_int_lit(the_node:Cint_lit,token:Symbol) : Any = {
    it.add(token)
  };

  override def visit_string_lit(the_node:Cstring_lit,token:Symbol) : Any  = {
    st.add(token)
  };
}
// #)
// PA6 Helper classes for inheritance graph and literal tables

// @(
class TempCalculator(var table : CodeInfoTable) extends CoolVisitor()
{
  var max : Int = 0;

  def set_max(curr : Int) : Unit =
    if (max < curr) max = curr else ();

  def get_max() : Int = max;

  def calc(e : Expression, curr : Int) : Unit = {
    table.set_info(e,curr);
    set_max(curr);
    e match {
      case n:Cno_expr => 
      case v:Cvariable => 
      case a:Cassign => calc(a.get_expr(),curr)

      case d:Cdispatch =>
	calc(d.get_expr(),curr);
	calc_exprs(d.get_actuals(),curr+1)
      case d:Cstatic_dispatch => 
	calc(d.get_expr(),curr);
	calc_exprs(d.get_actuals(),curr+1)

      case c:Ccond =>
	calc(c.get_pred(),curr);
        calc(c.get_then_exp(),curr);
        calc(c.get_else_exp(),curr)
      case l:Cloop =>
	calc(l.get_pred(),curr);
        calc(l.get_body(),curr)
      case c:Ctypecase =>
	calc(c.get_expr(),curr);
        calc_cases(c.get_cases(),curr)
      case b:Cblock => 
	calc_exprs(b.get_body(),curr)
      case l:Clet =>
	calc(l.get_init(),curr);
        calc(l.get_body(),curr+1)

      case op:Cadd =>
	calc_binary(op.get_e1(),op.get_e2(),curr)
      case op:Csub =>
	calc_binary(op.get_e1(),op.get_e2(),curr)
      case op:Cmul =>
	calc_binary(op.get_e1(),op.get_e2(),curr)
      case op:Cdiv =>
	calc_binary(op.get_e1(),op.get_e2(),curr)
      case op:Cneg =>
	calc(op.get_e1(),curr)
      case op:Clt =>
	calc_binary(op.get_e1(),op.get_e2(),curr)
      case op:Cleq =>
	calc_binary(op.get_e1(),op.get_e2(),curr)
      case op:Ccomp =>
	calc(op.get_e1(),curr)

      case l:Cint_lit => 
      case l:Cbool_lit =>
      case l:Cstring_lit =>

      case a:Calloc =>
      case u:Cunit =>
      case n:Cnil =>
    }
  };
    
  def calc_binary(e1 : Expression, e2 : Expression, curr : Int) : Unit = {
    calc(e1,curr);
    calc(e2,curr+1)
  };

  var current_offset : Int = 0;
  
  def calc_exprs(es : Expressions, curr : Int) : Unit = {
    set_max(curr);
    var saved : Int = current_offset;
    current_offset = curr;
    es.accept(this);
    current_offset = saved
  };

  def calc_cases(cs : Cases, curr : Int) : Unit = {
    set_max(curr+1); // in case there are no cases
    var saved : Int = current_offset;
    current_offset = curr;
    cs.accept(this);
    current_offset = saved
  };

  override def visit_Expressions_one(e : Expression) : Unit =
    calc(e,current_offset);

  override def visit_Cases_one(c : Case) : Unit =
    c match {
      case b:Cbranch =>
	table.set_info(b,current_offset);
        calc(b.get_expr(),current_offset+1)
    };
}
// @)
// ## PA7: helper class for computing temps
class OptGen(var p : Program, var opt : CoolOptions, var out : IO)
extends CodeGen(p,opt,out)
{
//#(
  var num_temp_regs : Int = 6; // s7 = GC limit pointer, s8 = $fp
  var max_reg : Int = 0;
  def temp_reg(t : Int) : String =
    "$s".concat((t - (t / num_temp_regs) * num_temp_regs + 1).toString());

  override def gen_temp(offset : Int) : String =
    if (offset + num_temp_regs < max_reg)
      emitter.gen_offset(emitter.s_FP(),offset+num_temp_regs)
    else if (max_reg <= offset)
      emitter.gen_offset(emitter.s_FP(),offset)
    else
      temp_reg(offset);

  override 
  def gen_method_body(formals : Formals, e : Expression, max : Int) : Any = {
    emitter.prologue(max);
    max_reg = max;
    var tregs : Int = max;
    if (num_temp_regs < tregs)
      tregs = num_temp_regs
    else ();
    var i : Int = 0;
    while (i < tregs) {
      emitter.opc("sw").opn(temp_reg(i)).opn(super.gen_temp(i)).endl(e);
      i = i + 1
    };
    code(e);
    i = 0;
    while (i < tregs) {
      emitter.opc("lw").opn(temp_reg(i)).opn(super.gen_temp(i)).endl(e);
      i = i + 1
    };
    emitter.epilogue(max,formals.size())
  };

  // generate code into $a0
  override def code(e : Expression) : Any = code_reg(e,acc);

  var ignore : String = "$zero";

  // generate code into register
  def code_reg(e : Expression, reg : String) : Any = {
    e match {
      case v:Cvariable =>
        if (reg == ignore) ()
	else if (v.get_name() == this_sym)
	  emitter.opc("move").opn(reg).opn(emitter.s_SELF()).endl(e)
	else {
	  var r : String = gen_binding(e.get_binding());
          if (r.charAt(0) == 36)
	    if (r == reg) () 
	    else emitter.opc("move").opn(reg).opn(r).endl(e)
	    else 
	      emitter.opc("lw").opn(reg).opn(r).endl(e)
	}

      case a:Cassign =>
	var r : String = gen_binding(e.get_binding());
        code(a.get_expr());
        if (r.charAt(0) == 36)
	  if (r == acc) () 
	  else emitter.opc("move").opn(r).opn(acc).endl(e)
	else {
	  emitter.opc("sw").opn(acc).opn(r).endl(e)
	};
        if (options.get_enable_gc()) {
          e.get_binding() match {
	    case at:Cattr =>
	      emitter.gc_assign(code_info_table.get_offset_info(at))
	    case x:CoolNode =>
	  }
	} else ();
        code_reg(new Cunit(),reg)

      case l:Clet => {
        var toff : Int = code_info_table.get_offset_info(l);
	if (l.get_identifier() == this_sym) {
	  code_reg(l.get_init(),acc);
	  code_spill(l.get_init(),toff,emitter.s_SELF());
	  emitter.opc("move").opn(emitter.s_SELF()).opn(acc).endl(l);
	  code_reg(l.get_body(),reg);
	  code_unspill(l,toff,emitter.s_SELF())
	} else {
	  code_spill_expr(l.get_init(),toff);
          code_reg(l.get_body(),reg)
	}
      }
      case a:Cadd => {
	var r1 : String = code_binary_int(e,a.get_e1(),a.get_e2(),true);
	emitter.opc("add").opn(t1).opn(r1).opn(t2).endl(e);
	emitter.opc("sw").opn(t1).offset(acc,emitter.i_ATTROFFSET()).endl(e);
	if (reg == acc) () else emitter.opc("move").opn(reg).opn(acc).endl(e)	
      }
      case a:Csub => {
	var r1 : String = code_binary_int(e,a.get_e1(),a.get_e2(),true);
	emitter.opc("sub").opn(t1).opn(r1).opn(t2).endl(e);
	emitter.opc("sw").opn(t1).offset(acc,emitter.i_ATTROFFSET()).endl(e);
	if (reg == acc) () else emitter.opc("move").opn(reg).opn(acc).endl(e)	
      }
      case a:Cmul => {
	var r1 : String = code_binary_int(e,a.get_e1(),a.get_e2(),true);
	emitter.opc("mulo").opn(t1).opn(r1).opn(t2).endl(e);
	emitter.opc("sw").opn(t1).offset(acc,emitter.i_ATTROFFSET()).endl(e);
	if (reg == acc) () else emitter.opc("move").opn(reg).opn(acc).endl(e)	
      }
      case a:Cdiv => {
	var r1 : String = code_binary_int(e,a.get_e1(),a.get_e2(),true);
	emitter.opc("div").opn(t1).opn(r1).opn(t2).endl(e);
	emitter.opc("sw").opn(t1).offset(acc,emitter.i_ATTROFFSET()).endl(e);
	if (reg == acc) () else emitter.opc("move").opn(reg).opn(acc).endl(e)	
      }
      case c:Ccond => {
	var else_label : String = gen_label();
        var done_label : String = gen_label();
        code_branch(c.get_pred(),else_label,false);
        code_reg(c.get_then_exp(),reg);
        emitter.opc("b").opn(done_label).endl(e);
        emitter.label_def(else_label);
        code_reg(c.get_else_exp(),reg);
        emitter.label_def(done_label)
      }
      case l:Cloop => {
        var body_label : String = gen_label();
	var pred_label : String = gen_label();
        emitter.opc("b").opn(pred_label).endl(e);
        emitter.label_def(body_label);
        code_reg(l.get_body(),ignore);
        emitter.label_def(pred_label);
        code_branch(l.get_pred(),body_label,true);
        if (reg == ignore) () else code_reg(new Cunit(),reg)
      }

      case l:Cint_lit =>
	if (reg == ignore) () else {
	var il : String = emitter.s_INTLIT(int_table.get(l.get_token()));
	emitter.opc("la").opn(reg).opn(il).endl(e)
	}

      case l:Cbool_lit =>
	if (reg == ignore) () else {
	var bl : String = emitter.s_BOOLEANLIT(l.get_value());
	emitter.opc("la").opn(reg).opn(bl).endl(e)
	}

      case l:Cstring_lit =>
	if (reg == ignore) () else {
        var sl : String = emitter.s_STRINGLIT(string_table.get(l.get_token()));
        emitter.opc("la").opn(reg).opn(sl).endl(e)
	}

      case u:Cunit =>
	if (reg == ignore) () 
	else emitter.opc("la").opn(reg).opn(emitter.s_UNITLIT()).endl(e)

      case u:Cnil => 
	if (reg == ignore) () 
	else emitter.opc("li").opn(reg).opn("0").endl(e)

      case x:Expression => {
	super.code(e);
	if (reg == acc) () 
	else if (reg == ignore) ()
	else emitter.opc("move").opn(reg).opn(acc).endl(e)
      }
    }
  };

  override def code_spill_expr(e : Expression, toff : Int) : String = {
    var tr : String = temp_reg(toff);
    code_reg(e, tr);
    code_spill(e,toff,tr);
    tr
  };

  def code_spill(e : Expression, toff : Int, reg : String) : Unit = {
    var spill : Boolean = num_temp_regs < max_reg - toff;
    if (spill) {
      emitter.opc("sw").opn(reg).opn(gen_temp(toff)).endl(e); ()
    } else ()
  };

  override def code_unspill(e : CoolNode, toff : Int, reg : String) : Any = {
    var spill : Boolean = num_temp_regs < max_reg - toff;
    if (spill) {
      emitter.opc("lw").opn(reg).opn(gen_temp(toff)).endl(e)
    } else {
      var tr : String = temp_reg(toff);
      if (tr == reg) () 
      else emitter.opc("move").opn(reg).opn(tr).endl(e)
    }
  };

  var exprs_left : Int = 0;

  override def code_exprs(es : Expressions) : Unit = {
    var saved_exprs_left : Int = exprs_left;
    exprs_left = es.size();
    super.code_exprs(es);
    exprs_left = saved_exprs_left
  };
  
  override def visit_Expressions_one(e : Expression) : Any = {
    if (is_actual)
      super.visit_Expressions_one(e)
    else {
      exprs_left = exprs_left - 1;
      if (exprs_left == 0) code(e)
      else code_reg(e,ignore)
    }
  };
  
  def is_scratch_reg(r : String) : Boolean =
    if (r == acc) true
    else if (r == "$t0") true
    else if (r == t1) true
    else if (r == t2) true
    else (r == ignore);

  // generate bare int into register
  def code_int(e : Expression, reg : String) : Any =
    if (if (options.get_enable_gc()) is_scratch_reg(reg) else true) {
      e match {
	case c:Ccond => {
	  var else_label : String = gen_label();
          var done_label : String = gen_label();
          code_branch(c.get_pred(),else_label,false);
          code_int(c.get_then_exp(),reg);
          emitter.opc("b").opn(done_label).endl(e);
          emitter.label_def(else_label);
          code_int(c.get_else_exp(),reg);
          emitter.label_def(done_label)
	}	  
	case a:Cadd => {
	  var r1 : String = code_binary_int(e,a.get_e1(),a.get_e2(),false);
	  emitter.opc("add").opn(reg).opn(r1).opn(t2).endl(e)	  
	}
	case a:Csub => {
	  var r1 : String = code_binary_int(e,a.get_e1(),a.get_e2(),false);
	  emitter.opc("sub").opn(reg).opn(r1).opn(t2).endl(e)	  
	}
	case a:Cmul => {
	  var r1 : String = code_binary_int(e,a.get_e1(),a.get_e2(),false);
	  emitter.opc("mulo").opn(reg).opn(r1).opn(t2).endl(e)	  
	}
	case a:Cdiv => {
	  var r1 : String = code_binary_int(e,a.get_e1(),a.get_e2(),false);
	  emitter.opc("div").opn(reg).opn(r1).opn(t2).endl(e)	  
	}
	case n:Cneg => {
	  code_int(n.get_e1(),reg);
	  emitter.opc("neg").opn(reg).opn(reg).endl(e)
	}
	case l:Cint_lit => {
	  emitter.opc("li").opn(reg).opn(symbol_name(l.get_token())).endl(e)
	}
	case x:Expression => {
	  code_reg(e,reg);
	  emitter.opc("lw").opn(reg).offset(reg,emitter.i_ATTROFFSET()).endl(e)
	}
      }
    } else code_reg(e,reg);

  def code_binary_int(op : CoolNode, e1 : Expression, e2 : Expression, copy : Boolean) : String = {
    emitter.out("# code_int ").out_any(copy).out("\n");
    var toff : Int = code_info_table.get_offset_info(op);
    var tr : String = temp_reg(toff);
    code_int(e1, tr);
    var spill : Boolean = num_temp_regs < max_reg - toff;
    if (spill) {
      emitter.opc("sw").opn(tr).opn(gen_temp(toff)).endl(e1)
    } else ();
    if (copy) {
      code(e2);
      emitter.opc("jal").opn(emitter.s_ANYCLONE()).endl(op);
      emitter.opc("lw").opn(t2).offset(acc,emitter.i_ATTROFFSET()).endl(op)
    } else {
      code_int(e2,t2)
    };
    if (spill) {
      emitter.opc("lw").opn(tr).opn(gen_temp(toff)).endl(op)
    } else ();
    if (options.get_enable_gc()) {
      emitter.opc("lw").opn(t1).offset(tr,emitter.i_ATTROFFSET()).endl(op);
      t1
    } else tr
  };

  // generate code for a boolean to cause jump to lab iff result is cond
  def code_branch(e : Expression, lab : String, cond : Boolean) : Any =
    e match {
      case a:Clt => {
	var r : String = code_binary_int(a,a.get_e1(),a.get_e2(),false);
	emitter.opc(if (cond) "blt" else "bge").opn(r).opn(t2).opn(lab).endl(e)
      }
      case a:Cleq => {
	var r : String = code_binary_int(a,a.get_e1(),a.get_e2(),false);
	emitter.opc(if (cond) "ble" else "bgt").opn(r).opn(t2).opn(lab).endl(e)
      }
      case a:Ccomp => {
	code_branch(a.get_e1(),lab,!cond)
      }
      case b:Cbool_lit => {
	if (b.get_value() == cond) emitter.opc("b").opn(lab).endl(e) else ()
      }
      case c:Ccond => {
	var else_label : String = gen_label();
        var done_label : String = gen_label();
        code_branch(c.get_pred(),else_label,false);
        code_branch(c.get_then_exp(),lab,cond);
        emitter.opc("b").opn(done_label).endl(e);
        emitter.label_def(else_label);
        code_branch(c.get_else_exp(),lab,cond);
        emitter.label_def(done_label)
      }
      case x:Expression => {
	code_reg(e,acc);
        emitter.opc("lw").opn(t1).offset(acc,emitter.i_ATTROFFSET()).endl(e);
        emitter.opc(if (cond) "bnez" else "beqz").opn(t1).opn(lab).endl(e)    
      }
    };
//#)
// 250 lines of Cool in our solution
}
// Automatically generated.  Do not edit!
class CoolNode() extends IO() {
  var id : Int = 0;
  def get_id() : Int = id;
  def set_id(i : Int) : Unit = id = i;

  var line_number : Int = 0;
  def get_line_number() : Int = line_number;
  def set_line_number(i : Int) : Unit = line_number = i;

  override def toString() : String = "@".concat(id.toString());

  def accept(visitor : CoolVisitor) : Any = null;
}

class Program() extends CoolNode() {
  var any_class:Class = null;
  def get_any_class() : Class = any_class;
  def set_any_class(arg : Class) : Unit = any_class = arg;

  var unit_class:Class = null;
  def get_unit_class() : Class = unit_class;
  def set_unit_class(arg : Class) : Unit = unit_class = arg;

  var int_class:Class = null;
  def get_int_class() : Class = int_class;
  def set_int_class(arg : Class) : Unit = int_class = arg;

  var boolean_class:Class = null;
  def get_boolean_class() : Class = boolean_class;
  def set_boolean_class(arg : Class) : Unit = boolean_class = arg;

  var string_class:Class = null;
  def get_string_class() : Class = string_class;
  def set_string_class(arg : Class) : Unit = string_class = arg;

}

class Class() extends CoolNode() {
  var superclass:Class = null;
  def get_superclass() : Class = superclass;
  def set_superclass(arg : Class) : Unit = superclass = arg;

  var inheritablep:Boolean = false;
  def get_inheritablep() : Boolean = inheritablep;
  def set_inheritablep(arg : Boolean) : Unit = inheritablep = arg;

}

class Classes() extends CoolNode() {
  def size() : Int = 0;

  def nth(i : Int) : Class = abort("no more elements");

  def concat(l : Classes) : Classes = new Classes_append(this,l);
  def addcopy(e : Class) : Classes = concat(new Classes_one(e));
  def elements() : ClassesEnumeration = new ClassesEnumeration(this);
}

class Classes_nil() extends Classes() {
  override def concat(l : Classes) : Classes = l;
}

class Classes_one(var arg : Class) extends Classes() {
  def get() : Class = arg;
  override def size() : Int = 1;
  override def nth(i : Int) : Class = if (i == 0) arg else super.nth(i);
  override def accept(v : CoolVisitor) : Any = v.visit_Classes_one(arg);
}

class Classes_append(var l1 : Classes, var l2 : Classes) extends Classes() {
  var n1 : Int = l1.size();
  var n2 : Int = l2.size();
  def get1() : Classes = l1;
  def get2() : Classes = l2;
  override def size() : Int = n1 + n2;
  override def nth(i : Int) : Class = if (i < n1) l1.nth(i) else l2.nth(i-n1);
  override def accept(v : CoolVisitor) : Any = {
    l1.accept(v);
    l2.accept(v);
    null  };
}

class ClassesEnumeration(var sequence : Classes) extends Enumeration() {
  var i : Int = -1;
  var n : Int = sequence.size();
  var a : ArrayAny = new ArrayAny(sequence.size());
  {
    var j : Int = 0;
    if (0 < n) a.set(0,sequence) else ();
    while (j < n) {
      a.get(j) match {
        case s:Classes_one => 
          a.set(j,s.get()); j = j+1
        case s:Classes_append => 
          var s1 : Classes = s.get1();
          var s2 : Classes = s.get2();
          var n1 : Int = s1.size();
          var n2 : Int = s2.size();
          if (0 < n1) a.set(j,s1) else ();
          if (0 < n2) a.set(j+n1,s2) else ()
      }
    }
  };

  override def hasNext() : Boolean = i+1 < n;
  override def next() : Class = {
    i = i + 1;    a.get(i) match {
      case x:Class => x
    }
  };

}

class Feature() extends CoolNode() {
  var owner:Cclass_decl = null;
  def get_owner() : Cclass_decl = owner;
  def set_owner(arg : Cclass_decl) : Unit = owner = arg;

  var overrides:Cmethod = null;
  def get_overrides() : Cmethod = overrides;
  def set_overrides(arg : Cmethod) : Unit = overrides = arg;

  var feature_of_class:Class = null;
  def get_feature_of_class() : Class = feature_of_class;
  def set_feature_of_class(arg : Class) : Unit = feature_of_class = arg;

}

class Features() extends CoolNode() {
  def size() : Int = 0;

  def nth(i : Int) : Feature = abort("no more elements");

  def concat(l : Features) : Features = new Features_append(this,l);
  def addcopy(e : Feature) : Features = concat(new Features_one(e));
  def elements() : FeaturesEnumeration = new FeaturesEnumeration(this);
}

class Features_nil() extends Features() {
  override def concat(l : Features) : Features = l;
}

class Features_one(var arg : Feature) extends Features() {
  def get() : Feature = arg;
  override def size() : Int = 1;
  override def nth(i : Int) : Feature = if (i == 0) arg else super.nth(i);
  override def accept(v : CoolVisitor) : Any = v.visit_Features_one(arg);
}

class Features_append(var l1 : Features, var l2 : Features) extends Features() {
  var n1 : Int = l1.size();
  var n2 : Int = l2.size();
  def get1() : Features = l1;
  def get2() : Features = l2;
  override def size() : Int = n1 + n2;
  override def nth(i : Int) : Feature = if (i < n1) l1.nth(i) else l2.nth(i-n1);
  override def accept(v : CoolVisitor) : Any = {
    l1.accept(v);
    l2.accept(v);
    null  };
}

class FeaturesEnumeration(var sequence : Features) extends Enumeration() {
  var i : Int = -1;
  var n : Int = sequence.size();
  var a : ArrayAny = new ArrayAny(sequence.size());
  {
    var j : Int = 0;
    if (0 < n) a.set(0,sequence) else ();
    while (j < n) {
      a.get(j) match {
        case s:Features_one => 
          a.set(j,s.get()); j = j+1
        case s:Features_append => 
          var s1 : Features = s.get1();
          var s2 : Features = s.get2();
          var n1 : Int = s1.size();
          var n2 : Int = s2.size();
          if (0 < n1) a.set(j,s1) else ();
          if (0 < n2) a.set(j+n1,s2) else ()
      }
    }
  };

  override def hasNext() : Boolean = i+1 < n;
  override def next() : Feature = {
    i = i + 1;    a.get(i) match {
      case x:Feature => x
    }
  };

}

class Formal() extends CoolNode() {
  var formal_of_class:Class = null;
  def get_formal_of_class() : Class = formal_of_class;
  def set_formal_of_class(arg : Class) : Unit = formal_of_class = arg;

}

class Formals() extends CoolNode() {
  def size() : Int = 0;

  def nth(i : Int) : Formal = abort("no more elements");

  def concat(l : Formals) : Formals = new Formals_append(this,l);
  def addcopy(e : Formal) : Formals = concat(new Formals_one(e));
  def elements() : FormalsEnumeration = new FormalsEnumeration(this);
}

class Formals_nil() extends Formals() {
  override def concat(l : Formals) : Formals = l;
}

class Formals_one(var arg : Formal) extends Formals() {
  def get() : Formal = arg;
  override def size() : Int = 1;
  override def nth(i : Int) : Formal = if (i == 0) arg else super.nth(i);
  override def accept(v : CoolVisitor) : Any = v.visit_Formals_one(arg);
}

class Formals_append(var l1 : Formals, var l2 : Formals) extends Formals() {
  var n1 : Int = l1.size();
  var n2 : Int = l2.size();
  def get1() : Formals = l1;
  def get2() : Formals = l2;
  override def size() : Int = n1 + n2;
  override def nth(i : Int) : Formal = if (i < n1) l1.nth(i) else l2.nth(i-n1);
  override def accept(v : CoolVisitor) : Any = {
    l1.accept(v);
    l2.accept(v);
    null  };
}

class FormalsEnumeration(var sequence : Formals) extends Enumeration() {
  var i : Int = -1;
  var n : Int = sequence.size();
  var a : ArrayAny = new ArrayAny(sequence.size());
  {
    var j : Int = 0;
    if (0 < n) a.set(0,sequence) else ();
    while (j < n) {
      a.get(j) match {
        case s:Formals_one => 
          a.set(j,s.get()); j = j+1
        case s:Formals_append => 
          var s1 : Formals = s.get1();
          var s2 : Formals = s.get2();
          var n1 : Int = s1.size();
          var n2 : Int = s2.size();
          if (0 < n1) a.set(j,s1) else ();
          if (0 < n2) a.set(j+n1,s2) else ()
      }
    }
  };

  override def hasNext() : Boolean = i+1 < n;
  override def next() : Formal = {
    i = i + 1;    a.get(i) match {
      case x:Formal => x
    }
  };

}

class Expression() extends CoolNode() {
  var of_type:Symbol = null;
  def get_of_type() : Symbol = of_type;
  def set_of_type(arg : Symbol) : Unit = of_type = arg;

  var of_class:Class = null;
  def get_of_class() : Class = of_class;
  def set_of_class(arg : Class) : Unit = of_class = arg;

  var binding:CoolNode = null;
  def get_binding() : CoolNode = binding;
  def set_binding(arg : CoolNode) : Unit = binding = arg;

  var mbinding:Cmethod = null;
  def get_mbinding() : Cmethod = mbinding;
  def set_mbinding(arg : Cmethod) : Unit = mbinding = arg;

}

class Expressions() extends CoolNode() {
  def size() : Int = 0;

  def nth(i : Int) : Expression = abort("no more elements");

  def concat(l : Expressions) : Expressions = new Expressions_append(this,l);
  def addcopy(e : Expression) : Expressions = concat(new Expressions_one(e));
  def elements() : ExpressionsEnumeration = new ExpressionsEnumeration(this);
}

class Expressions_nil() extends Expressions() {
  override def concat(l : Expressions) : Expressions = l;
}

class Expressions_one(var arg : Expression) extends Expressions() {
  def get() : Expression = arg;
  override def size() : Int = 1;
  override def nth(i : Int) : Expression = if (i == 0) arg else super.nth(i);
  override def accept(v : CoolVisitor) : Any = v.visit_Expressions_one(arg);
}

class Expressions_append(var l1 : Expressions, var l2 : Expressions) extends Expressions() {
  var n1 : Int = l1.size();
  var n2 : Int = l2.size();
  def get1() : Expressions = l1;
  def get2() : Expressions = l2;
  override def size() : Int = n1 + n2;
  override def nth(i : Int) : Expression = if (i < n1) l1.nth(i) else l2.nth(i-n1);
  override def accept(v : CoolVisitor) : Any = {
    l1.accept(v);
    l2.accept(v);
    null  };
}

class ExpressionsEnumeration(var sequence : Expressions) extends Enumeration() {
  var i : Int = -1;
  var n : Int = sequence.size();
  var a : ArrayAny = new ArrayAny(sequence.size());
  {
    var j : Int = 0;
    if (0 < n) a.set(0,sequence) else ();
    while (j < n) {
      a.get(j) match {
        case s:Expressions_one => 
          a.set(j,s.get()); j = j+1
        case s:Expressions_append => 
          var s1 : Expressions = s.get1();
          var s2 : Expressions = s.get2();
          var n1 : Int = s1.size();
          var n2 : Int = s2.size();
          if (0 < n1) a.set(j,s1) else ();
          if (0 < n2) a.set(j+n1,s2) else ()
      }
    }
  };

  override def hasNext() : Boolean = i+1 < n;
  override def next() : Expression = {
    i = i + 1;    a.get(i) match {
      case x:Expression => x
    }
  };

}

class Case() extends CoolNode() {
  var case_of_type:Symbol = null;
  def get_case_of_type() : Symbol = case_of_type;
  def set_case_of_type(arg : Symbol) : Unit = case_of_type = arg;

  var case_of_class:Class = null;
  def get_case_of_class() : Class = case_of_class;
  def set_case_of_class(arg : Class) : Unit = case_of_class = arg;

}

class Cases() extends CoolNode() {
  def size() : Int = 0;

  def nth(i : Int) : Case = abort("no more elements");

  def concat(l : Cases) : Cases = new Cases_append(this,l);
  def addcopy(e : Case) : Cases = concat(new Cases_one(e));
  def elements() : CasesEnumeration = new CasesEnumeration(this);
}

class Cases_nil() extends Cases() {
  override def concat(l : Cases) : Cases = l;
}

class Cases_one(var arg : Case) extends Cases() {
  def get() : Case = arg;
  override def size() : Int = 1;
  override def nth(i : Int) : Case = if (i == 0) arg else super.nth(i);
  override def accept(v : CoolVisitor) : Any = v.visit_Cases_one(arg);
}

class Cases_append(var l1 : Cases, var l2 : Cases) extends Cases() {
  var n1 : Int = l1.size();
  var n2 : Int = l2.size();
  def get1() : Cases = l1;
  def get2() : Cases = l2;
  override def size() : Int = n1 + n2;
  override def nth(i : Int) : Case = if (i < n1) l1.nth(i) else l2.nth(i-n1);
  override def accept(v : CoolVisitor) : Any = {
    l1.accept(v);
    l2.accept(v);
    null  };
}

class CasesEnumeration(var sequence : Cases) extends Enumeration() {
  var i : Int = -1;
  var n : Int = sequence.size();
  var a : ArrayAny = new ArrayAny(sequence.size());
  {
    var j : Int = 0;
    if (0 < n) a.set(0,sequence) else ();
    while (j < n) {
      a.get(j) match {
        case s:Cases_one => 
          a.set(j,s.get()); j = j+1
        case s:Cases_append => 
          var s1 : Cases = s.get1();
          var s2 : Cases = s.get2();
          var n1 : Int = s1.size();
          var n2 : Int = s2.size();
          if (0 < n1) a.set(j,s1) else ();
          if (0 < n2) a.set(j+n1,s2) else ()
      }
    }
  };

  override def hasNext() : Boolean = i+1 < n;
  override def next() : Case = {
    i = i + 1;    a.get(i) match {
      case x:Case => x
    }
  };

}

class Cprogram(var classes:Classes) extends Program() {
  def get_classes() : Classes = classes;
  def set_classes(new_classes : Classes) :Unit = classes = new_classes;

  override def accept(v : CoolVisitor) : Any = v.visit_program(this,classes);
}

class Cclass_decl(var name:Symbol,var parent:Symbol,var features:Features,var filename:Symbol) extends Class() {
  def get_name() : Symbol = name;
  def set_name(new_name : Symbol) :Unit = name = new_name;
  def get_parent() : Symbol = parent;
  def set_parent(new_parent : Symbol) :Unit = parent = new_parent;
  def get_features() : Features = features;
  def set_features(new_features : Features) :Unit = features = new_features;
  def get_filename() : Symbol = filename;
  def set_filename(new_filename : Symbol) :Unit = filename = new_filename;

  override def accept(v : CoolVisitor) : Any = v.visit_class_decl(this,name,parent,features,filename);
}

class Cmethod(var overridep:Boolean,var name:Symbol,var formals:Formals,var return_type:Symbol,var expr:Expression) extends Feature() {
  def get_overridep() : Boolean = overridep;
  def set_overridep(new_overridep : Boolean) :Unit = overridep = new_overridep;
  def get_name() : Symbol = name;
  def set_name(new_name : Symbol) :Unit = name = new_name;
  def get_formals() : Formals = formals;
  def set_formals(new_formals : Formals) :Unit = formals = new_formals;
  def get_return_type() : Symbol = return_type;
  def set_return_type(new_return_type : Symbol) :Unit = return_type = new_return_type;
  def get_expr() : Expression = expr;
  def set_expr(new_expr : Expression) :Unit = expr = new_expr;

  override def accept(v : CoolVisitor) : Any = v.visit_method(this,overridep,name,formals,return_type,expr);
}

class Cattr(var name:Symbol,var of_type:Symbol) extends Feature() {
  def get_name() : Symbol = name;
  def set_name(new_name : Symbol) :Unit = name = new_name;
  def get_of_type() : Symbol = of_type;
  def set_of_type(new_of_type : Symbol) :Unit = of_type = new_of_type;

  override def accept(v : CoolVisitor) : Any = v.visit_attr(this,name,of_type);
}

class Cformal(var name:Symbol,var of_type:Symbol) extends Formal() {
  def get_name() : Symbol = name;
  def set_name(new_name : Symbol) :Unit = name = new_name;
  def get_of_type() : Symbol = of_type;
  def set_of_type(new_of_type : Symbol) :Unit = of_type = new_of_type;

  override def accept(v : CoolVisitor) : Any = v.visit_formal(this,name,of_type);
}

class Cbranch(var name:Symbol,var local_type:Symbol,var expr:Expression) extends Case() {
  def get_name() : Symbol = name;
  def set_name(new_name : Symbol) :Unit = name = new_name;
  def get_local_type() : Symbol = local_type;
  def set_local_type(new_local_type : Symbol) :Unit = local_type = new_local_type;
  def get_expr() : Expression = expr;
  def set_expr(new_expr : Expression) :Unit = expr = new_expr;

  override def accept(v : CoolVisitor) : Any = v.visit_branch(this,name,local_type,expr);
}

class Cassign(var name:Symbol,var expr:Expression) extends Expression() {
  def get_name() : Symbol = name;
  def set_name(new_name : Symbol) :Unit = name = new_name;
  def get_expr() : Expression = expr;
  def set_expr(new_expr : Expression) :Unit = expr = new_expr;

  override def accept(v : CoolVisitor) : Any = v.visit_assign(this,name,expr);
}

class Cstatic_dispatch(var expr:Expression,var type_name:Symbol,var name:Symbol,var actuals:Expressions) extends Expression() {
  def get_expr() : Expression = expr;
  def set_expr(new_expr : Expression) :Unit = expr = new_expr;
  def get_type_name() : Symbol = type_name;
  def set_type_name(new_type_name : Symbol) :Unit = type_name = new_type_name;
  def get_name() : Symbol = name;
  def set_name(new_name : Symbol) :Unit = name = new_name;
  def get_actuals() : Expressions = actuals;
  def set_actuals(new_actuals : Expressions) :Unit = actuals = new_actuals;

  override def accept(v : CoolVisitor) : Any = v.visit_static_dispatch(this,expr,type_name,name,actuals);
}

class Cdispatch(var expr:Expression,var name:Symbol,var actuals:Expressions) extends Expression() {
  def get_expr() : Expression = expr;
  def set_expr(new_expr : Expression) :Unit = expr = new_expr;
  def get_name() : Symbol = name;
  def set_name(new_name : Symbol) :Unit = name = new_name;
  def get_actuals() : Expressions = actuals;
  def set_actuals(new_actuals : Expressions) :Unit = actuals = new_actuals;

  override def accept(v : CoolVisitor) : Any = v.visit_dispatch(this,expr,name,actuals);
}

class Ccond(var pred:Expression,var then_exp:Expression,var else_exp:Expression) extends Expression() {
  def get_pred() : Expression = pred;
  def set_pred(new_pred : Expression) :Unit = pred = new_pred;
  def get_then_exp() : Expression = then_exp;
  def set_then_exp(new_then_exp : Expression) :Unit = then_exp = new_then_exp;
  def get_else_exp() : Expression = else_exp;
  def set_else_exp(new_else_exp : Expression) :Unit = else_exp = new_else_exp;

  override def accept(v : CoolVisitor) : Any = v.visit_cond(this,pred,then_exp,else_exp);
}

class Cloop(var pred:Expression,var body:Expression) extends Expression() {
  def get_pred() : Expression = pred;
  def set_pred(new_pred : Expression) :Unit = pred = new_pred;
  def get_body() : Expression = body;
  def set_body(new_body : Expression) :Unit = body = new_body;

  override def accept(v : CoolVisitor) : Any = v.visit_loop(this,pred,body);
}

class Ctypecase(var expr:Expression,var cases:Cases) extends Expression() {
  def get_expr() : Expression = expr;
  def set_expr(new_expr : Expression) :Unit = expr = new_expr;
  def get_cases() : Cases = cases;
  def set_cases(new_cases : Cases) :Unit = cases = new_cases;

  override def accept(v : CoolVisitor) : Any = v.visit_typecase(this,expr,cases);
}

class Cblock(var body:Expressions) extends Expression() {
  def get_body() : Expressions = body;
  def set_body(new_body : Expressions) :Unit = body = new_body;

  override def accept(v : CoolVisitor) : Any = v.visit_block(this,body);
}

class Clet(var identifier:Symbol,var local_type:Symbol,var init:Expression,var body:Expression) extends Expression() {
  def get_identifier() : Symbol = identifier;
  def set_identifier(new_identifier : Symbol) :Unit = identifier = new_identifier;
  def get_local_type() : Symbol = local_type;
  def set_local_type(new_local_type : Symbol) :Unit = local_type = new_local_type;
  def get_init() : Expression = init;
  def set_init(new_init : Expression) :Unit = init = new_init;
  def get_body() : Expression = body;
  def set_body(new_body : Expression) :Unit = body = new_body;

  override def accept(v : CoolVisitor) : Any = v.visit_let(this,identifier,local_type,init,body);
}

class Cadd(var e1:Expression,var e2:Expression) extends Expression() {
  def get_e1() : Expression = e1;
  def set_e1(new_e1 : Expression) :Unit = e1 = new_e1;
  def get_e2() : Expression = e2;
  def set_e2(new_e2 : Expression) :Unit = e2 = new_e2;

  override def accept(v : CoolVisitor) : Any = v.visit_add(this,e1,e2);
}

class Csub(var e1:Expression,var e2:Expression) extends Expression() {
  def get_e1() : Expression = e1;
  def set_e1(new_e1 : Expression) :Unit = e1 = new_e1;
  def get_e2() : Expression = e2;
  def set_e2(new_e2 : Expression) :Unit = e2 = new_e2;

  override def accept(v : CoolVisitor) : Any = v.visit_sub(this,e1,e2);
}

class Cmul(var e1:Expression,var e2:Expression) extends Expression() {
  def get_e1() : Expression = e1;
  def set_e1(new_e1 : Expression) :Unit = e1 = new_e1;
  def get_e2() : Expression = e2;
  def set_e2(new_e2 : Expression) :Unit = e2 = new_e2;

  override def accept(v : CoolVisitor) : Any = v.visit_mul(this,e1,e2);
}

class Cdiv(var e1:Expression,var e2:Expression) extends Expression() {
  def get_e1() : Expression = e1;
  def set_e1(new_e1 : Expression) :Unit = e1 = new_e1;
  def get_e2() : Expression = e2;
  def set_e2(new_e2 : Expression) :Unit = e2 = new_e2;

  override def accept(v : CoolVisitor) : Any = v.visit_div(this,e1,e2);
}

class Cneg(var e1:Expression) extends Expression() {
  def get_e1() : Expression = e1;
  def set_e1(new_e1 : Expression) :Unit = e1 = new_e1;

  override def accept(v : CoolVisitor) : Any = v.visit_neg(this,e1);
}

class Clt(var e1:Expression,var e2:Expression) extends Expression() {
  def get_e1() : Expression = e1;
  def set_e1(new_e1 : Expression) :Unit = e1 = new_e1;
  def get_e2() : Expression = e2;
  def set_e2(new_e2 : Expression) :Unit = e2 = new_e2;

  override def accept(v : CoolVisitor) : Any = v.visit_lt(this,e1,e2);
}

class Cleq(var e1:Expression,var e2:Expression) extends Expression() {
  def get_e1() : Expression = e1;
  def set_e1(new_e1 : Expression) :Unit = e1 = new_e1;
  def get_e2() : Expression = e2;
  def set_e2(new_e2 : Expression) :Unit = e2 = new_e2;

  override def accept(v : CoolVisitor) : Any = v.visit_leq(this,e1,e2);
}

class Ccomp(var e1:Expression) extends Expression() {
  def get_e1() : Expression = e1;
  def set_e1(new_e1 : Expression) :Unit = e1 = new_e1;

  override def accept(v : CoolVisitor) : Any = v.visit_comp(this,e1);
}

class Cint_lit(var token:Symbol) extends Expression() {
  def get_token() : Symbol = token;
  def set_token(new_token : Symbol) :Unit = token = new_token;

  override def accept(v : CoolVisitor) : Any = v.visit_int_lit(this,token);
}

class Cbool_lit(var value:Boolean) extends Expression() {
  def get_value() : Boolean = value;
  def set_value(new_value : Boolean) :Unit = value = new_value;

  override def accept(v : CoolVisitor) : Any = v.visit_bool_lit(this,value);
}

class Cstring_lit(var token:Symbol) extends Expression() {
  def get_token() : Symbol = token;
  def set_token(new_token : Symbol) :Unit = token = new_token;

  override def accept(v : CoolVisitor) : Any = v.visit_string_lit(this,token);
}

class Calloc(var type_name:Symbol) extends Expression() {
  def get_type_name() : Symbol = type_name;
  def set_type_name(new_type_name : Symbol) :Unit = type_name = new_type_name;

  override def accept(v : CoolVisitor) : Any = v.visit_alloc(this,type_name);
}

class Cnil() extends Expression() {

  override def accept(v : CoolVisitor) : Any = v.visit_nil(this);
}

class Cunit() extends Expression() {

  override def accept(v : CoolVisitor) : Any = v.visit_unit(this);
}

class Cno_expr() extends Expression() {

  override def accept(v : CoolVisitor) : Any = v.visit_no_expr(this);
}

class Cvariable(var name:Symbol) extends Expression() {
  def get_name() : Symbol = name;
  def set_name(new_name : Symbol) :Unit = name = new_name;

  override def accept(v : CoolVisitor) : Any = v.visit_variable(this,name);
}
// Automatically generated.  Do not edit!
class CoolNodeFactory(var node_id : Int) {
  def get_line_number() : Int = 0;

  def get_node_number() : Int = {
    node_id = node_id + 1; node_id
  };
  def set_node_numbers(n: CoolNode) : Unit = {
    n.set_id(get_node_number());
    n.set_line_number(get_line_number())
  };

  def program(classes:Classes) : Cprogram = {
    var n : Cprogram = new Cprogram(classes);
    set_node_numbers(n);
    n
  };

  def class_decl(name:Symbol,parent:Symbol,features:Features,filename:Symbol) : Cclass_decl = {
    var n : Cclass_decl = new Cclass_decl(name,parent,features,filename);
    set_node_numbers(n);
    n
  };

  def method(overridep:Boolean,name:Symbol,formals:Formals,return_type:Symbol,expr:Expression) : Cmethod = {
    var n : Cmethod = new Cmethod(overridep,name,formals,return_type,expr);
    set_node_numbers(n);
    n
  };

  def attr(name:Symbol,of_type:Symbol) : Cattr = {
    var n : Cattr = new Cattr(name,of_type);
    set_node_numbers(n);
    n
  };

  def formal(name:Symbol,of_type:Symbol) : Cformal = {
    var n : Cformal = new Cformal(name,of_type);
    set_node_numbers(n);
    n
  };

  def branch(name:Symbol,local_type:Symbol,expr:Expression) : Cbranch = {
    var n : Cbranch = new Cbranch(name,local_type,expr);
    set_node_numbers(n);
    n
  };

  def assign(name:Symbol,expr:Expression) : Cassign = {
    var n : Cassign = new Cassign(name,expr);
    set_node_numbers(n);
    n
  };

  def static_dispatch(expr:Expression,type_name:Symbol,name:Symbol,actuals:Expressions) : Cstatic_dispatch = {
    var n : Cstatic_dispatch = new Cstatic_dispatch(expr,type_name,name,actuals);
    set_node_numbers(n);
    n
  };

  def dispatch(expr:Expression,name:Symbol,actuals:Expressions) : Cdispatch = {
    var n : Cdispatch = new Cdispatch(expr,name,actuals);
    set_node_numbers(n);
    n
  };

  def cond(pred:Expression,then_exp:Expression,else_exp:Expression) : Ccond = {
    var n : Ccond = new Ccond(pred,then_exp,else_exp);
    set_node_numbers(n);
    n
  };

  def loop(pred:Expression,body:Expression) : Cloop = {
    var n : Cloop = new Cloop(pred,body);
    set_node_numbers(n);
    n
  };

  def typecase(expr:Expression,cases:Cases) : Ctypecase = {
    var n : Ctypecase = new Ctypecase(expr,cases);
    set_node_numbers(n);
    n
  };

  def block(body:Expressions) : Cblock = {
    var n : Cblock = new Cblock(body);
    set_node_numbers(n);
    n
  };

  def let(identifier:Symbol,local_type:Symbol,init:Expression,body:Expression) : Clet = {
    var n : Clet = new Clet(identifier,local_type,init,body);
    set_node_numbers(n);
    n
  };

  def add(e1:Expression,e2:Expression) : Cadd = {
    var n : Cadd = new Cadd(e1,e2);
    set_node_numbers(n);
    n
  };

  def sub(e1:Expression,e2:Expression) : Csub = {
    var n : Csub = new Csub(e1,e2);
    set_node_numbers(n);
    n
  };

  def mul(e1:Expression,e2:Expression) : Cmul = {
    var n : Cmul = new Cmul(e1,e2);
    set_node_numbers(n);
    n
  };

  def div(e1:Expression,e2:Expression) : Cdiv = {
    var n : Cdiv = new Cdiv(e1,e2);
    set_node_numbers(n);
    n
  };

  def neg(e1:Expression) : Cneg = {
    var n : Cneg = new Cneg(e1);
    set_node_numbers(n);
    n
  };

  def lt(e1:Expression,e2:Expression) : Clt = {
    var n : Clt = new Clt(e1,e2);
    set_node_numbers(n);
    n
  };

  def leq(e1:Expression,e2:Expression) : Cleq = {
    var n : Cleq = new Cleq(e1,e2);
    set_node_numbers(n);
    n
  };

  def comp(e1:Expression) : Ccomp = {
    var n : Ccomp = new Ccomp(e1);
    set_node_numbers(n);
    n
  };

  def int_lit(token:Symbol) : Cint_lit = {
    var n : Cint_lit = new Cint_lit(token);
    set_node_numbers(n);
    n
  };

  def bool_lit(value:Boolean) : Cbool_lit = {
    var n : Cbool_lit = new Cbool_lit(value);
    set_node_numbers(n);
    n
  };

  def string_lit(token:Symbol) : Cstring_lit = {
    var n : Cstring_lit = new Cstring_lit(token);
    set_node_numbers(n);
    n
  };

  def alloc(type_name:Symbol) : Calloc = {
    var n : Calloc = new Calloc(type_name);
    set_node_numbers(n);
    n
  };

  def nil() : Cnil = {
    var n : Cnil = new Cnil();
    set_node_numbers(n);
    n
  };

  def unit() : Cunit = {
    var n : Cunit = new Cunit();
    set_node_numbers(n);
    n
  };

  def no_expr() : Cno_expr = {
    var n : Cno_expr = new Cno_expr();
    set_node_numbers(n);
    n
  };

  def variable(name:Symbol) : Cvariable = {
    var n : Cvariable = new Cvariable(name);
    set_node_numbers(n);
    n
  };
}
// Automatically generated.  Do not edit!
class CoolVisitor() extends IO() {
  def visit_CoolNode(node:CoolNode) : Any = {
    abort("No visitor for ".concat(node.toString()))
  };

  def visit_Program(node:Program) : Any = visit_CoolNode(node);

  def visit_Class(node:Class) : Any = visit_CoolNode(node);

  def visit_Classes_one(node:Class) : Any = 
    abort("No visitor for Classes elements");

  def visit_Feature(node:Feature) : Any = visit_CoolNode(node);

  def visit_Features_one(node:Feature) : Any = 
    abort("No visitor for Features elements");

  def visit_Formal(node:Formal) : Any = visit_CoolNode(node);

  def visit_Formals_one(node:Formal) : Any = 
    abort("No visitor for Formals elements");

  def visit_Expression(node:Expression) : Any = visit_CoolNode(node);

  def visit_Expressions_one(node:Expression) : Any = 
    abort("No visitor for Expressions elements");

  def visit_Case(node:Case) : Any = visit_CoolNode(node);

  def visit_Cases_one(node:Case) : Any = 
    abort("No visitor for Cases elements");

  def visit_program(the_node:Cprogram,classes:Classes) : Any = 
    visit_Program(the_node);

  def visit_class_decl(the_node:Cclass_decl,name:Symbol,parent:Symbol,features:Features,filename:Symbol) : Any = 
    visit_Class(the_node);

  def visit_method(the_node:Cmethod,overridep:Boolean,name:Symbol,formals:Formals,return_type:Symbol,expr:Expression) : Any = 
    visit_Feature(the_node);

  def visit_attr(the_node:Cattr,name:Symbol,of_type:Symbol) : Any = 
    visit_Feature(the_node);

  def visit_formal(the_node:Cformal,name:Symbol,of_type:Symbol) : Any = 
    visit_Formal(the_node);

  def visit_branch(the_node:Cbranch,name:Symbol,local_type:Symbol,expr:Expression) : Any = 
    visit_Case(the_node);

  def visit_assign(the_node:Cassign,name:Symbol,expr:Expression) : Any = 
    visit_Expression(the_node);

  def visit_static_dispatch(the_node:Cstatic_dispatch,expr:Expression,type_name:Symbol,name:Symbol,actuals:Expressions) : Any = 
    visit_Expression(the_node);

  def visit_dispatch(the_node:Cdispatch,expr:Expression,name:Symbol,actuals:Expressions) : Any = 
    visit_Expression(the_node);

  def visit_cond(the_node:Ccond,pred:Expression,then_exp:Expression,else_exp:Expression) : Any = 
    visit_Expression(the_node);

  def visit_loop(the_node:Cloop,pred:Expression,body:Expression) : Any = 
    visit_Expression(the_node);

  def visit_typecase(the_node:Ctypecase,expr:Expression,cases:Cases) : Any = 
    visit_Expression(the_node);

  def visit_block(the_node:Cblock,body:Expressions) : Any = 
    visit_Expression(the_node);

  def visit_let(the_node:Clet,identifier:Symbol,local_type:Symbol,init:Expression,body:Expression) : Any = 
    visit_Expression(the_node);

  def visit_add(the_node:Cadd,e1:Expression,e2:Expression) : Any = 
    visit_Expression(the_node);

  def visit_sub(the_node:Csub,e1:Expression,e2:Expression) : Any = 
    visit_Expression(the_node);

  def visit_mul(the_node:Cmul,e1:Expression,e2:Expression) : Any = 
    visit_Expression(the_node);

  def visit_div(the_node:Cdiv,e1:Expression,e2:Expression) : Any = 
    visit_Expression(the_node);

  def visit_neg(the_node:Cneg,e1:Expression) : Any = 
    visit_Expression(the_node);

  def visit_lt(the_node:Clt,e1:Expression,e2:Expression) : Any = 
    visit_Expression(the_node);

  def visit_leq(the_node:Cleq,e1:Expression,e2:Expression) : Any = 
    visit_Expression(the_node);

  def visit_comp(the_node:Ccomp,e1:Expression) : Any = 
    visit_Expression(the_node);

  def visit_int_lit(the_node:Cint_lit,token:Symbol) : Any = 
    visit_Expression(the_node);

  def visit_bool_lit(the_node:Cbool_lit,value:Boolean) : Any = 
    visit_Expression(the_node);

  def visit_string_lit(the_node:Cstring_lit,token:Symbol) : Any = 
    visit_Expression(the_node);

  def visit_alloc(the_node:Calloc,type_name:Symbol) : Any = 
    visit_Expression(the_node);

  def visit_nil(the_node:Cnil) : Any = 
    visit_Expression(the_node);

  def visit_unit(the_node:Cunit) : Any = 
    visit_Expression(the_node);

  def visit_no_expr(the_node:Cno_expr) : Any = 
    visit_Expression(the_node);

  def visit_variable(the_node:Cvariable,name:Symbol) : Any = 
    visit_Expression(the_node);
}
// Automatically generated.  Do not edit!
class CoolTreeVisitor() extends CoolVisitor() {
  override def visit_CoolNode(node:CoolNode) : Any = null;

  override def visit_Classes_one(node:Class) : Any = node.accept(this);

  override def visit_Features_one(node:Feature) : Any = node.accept(this);

  override def visit_Formals_one(node:Formal) : Any = node.accept(this);

  override def visit_Expressions_one(node:Expression) : Any = node.accept(this);

  override def visit_Cases_one(node:Case) : Any = node.accept(this);

  override def visit_program(the_node:Cprogram,classes:Classes) : Any = {
    visit_Program(the_node);
    classes.accept(this);
    null
  };

  override def visit_class_decl(the_node:Cclass_decl,name:Symbol,parent:Symbol,features:Features,filename:Symbol) : Any = {
    visit_Class(the_node);
    features.accept(this);
    null
  };

  override def visit_method(the_node:Cmethod,overridep:Boolean,name:Symbol,formals:Formals,return_type:Symbol,expr:Expression) : Any = {
    visit_Feature(the_node);
    formals.accept(this);
    expr.accept(this);
    null
  };

  override def visit_attr(the_node:Cattr,name:Symbol,of_type:Symbol) : Any = {
    visit_Feature(the_node);
    null
  };

  override def visit_formal(the_node:Cformal,name:Symbol,of_type:Symbol) : Any = {
    visit_Formal(the_node);
    null
  };

  override def visit_branch(the_node:Cbranch,name:Symbol,local_type:Symbol,expr:Expression) : Any = {
    visit_Case(the_node);
    expr.accept(this);
    null
  };

  override def visit_assign(the_node:Cassign,name:Symbol,expr:Expression) : Any = {
    visit_Expression(the_node);
    expr.accept(this);
    null
  };

  override def visit_static_dispatch(the_node:Cstatic_dispatch,expr:Expression,type_name:Symbol,name:Symbol,actuals:Expressions) : Any = {
    visit_Expression(the_node);
    expr.accept(this);
    actuals.accept(this);
    null
  };

  override def visit_dispatch(the_node:Cdispatch,expr:Expression,name:Symbol,actuals:Expressions) : Any = {
    visit_Expression(the_node);
    expr.accept(this);
    actuals.accept(this);
    null
  };

  override def visit_cond(the_node:Ccond,pred:Expression,then_exp:Expression,else_exp:Expression) : Any = {
    visit_Expression(the_node);
    pred.accept(this);
    then_exp.accept(this);
    else_exp.accept(this);
    null
  };

  override def visit_loop(the_node:Cloop,pred:Expression,body:Expression) : Any = {
    visit_Expression(the_node);
    pred.accept(this);
    body.accept(this);
    null
  };

  override def visit_typecase(the_node:Ctypecase,expr:Expression,cases:Cases) : Any = {
    visit_Expression(the_node);
    expr.accept(this);
    cases.accept(this);
    null
  };

  override def visit_block(the_node:Cblock,body:Expressions) : Any = {
    visit_Expression(the_node);
    body.accept(this);
    null
  };

  override def visit_let(the_node:Clet,identifier:Symbol,local_type:Symbol,init:Expression,body:Expression) : Any = {
    visit_Expression(the_node);
    init.accept(this);
    body.accept(this);
    null
  };

  override def visit_add(the_node:Cadd,e1:Expression,e2:Expression) : Any = {
    visit_Expression(the_node);
    e1.accept(this);
    e2.accept(this);
    null
  };

  override def visit_sub(the_node:Csub,e1:Expression,e2:Expression) : Any = {
    visit_Expression(the_node);
    e1.accept(this);
    e2.accept(this);
    null
  };

  override def visit_mul(the_node:Cmul,e1:Expression,e2:Expression) : Any = {
    visit_Expression(the_node);
    e1.accept(this);
    e2.accept(this);
    null
  };

  override def visit_div(the_node:Cdiv,e1:Expression,e2:Expression) : Any = {
    visit_Expression(the_node);
    e1.accept(this);
    e2.accept(this);
    null
  };

  override def visit_neg(the_node:Cneg,e1:Expression) : Any = {
    visit_Expression(the_node);
    e1.accept(this);
    null
  };

  override def visit_lt(the_node:Clt,e1:Expression,e2:Expression) : Any = {
    visit_Expression(the_node);
    e1.accept(this);
    e2.accept(this);
    null
  };

  override def visit_leq(the_node:Cleq,e1:Expression,e2:Expression) : Any = {
    visit_Expression(the_node);
    e1.accept(this);
    e2.accept(this);
    null
  };

  override def visit_comp(the_node:Ccomp,e1:Expression) : Any = {
    visit_Expression(the_node);
    e1.accept(this);
    null
  };

  override def visit_int_lit(the_node:Cint_lit,token:Symbol) : Any = {
    visit_Expression(the_node);
    null
  };

  override def visit_bool_lit(the_node:Cbool_lit,value:Boolean) : Any = {
    visit_Expression(the_node);
    null
  };

  override def visit_string_lit(the_node:Cstring_lit,token:Symbol) : Any = {
    visit_Expression(the_node);
    null
  };

  override def visit_alloc(the_node:Calloc,type_name:Symbol) : Any = {
    visit_Expression(the_node);
    null
  };

  override def visit_nil(the_node:Cnil) : Any = {
    visit_Expression(the_node);
    null
  };

  override def visit_unit(the_node:Cunit) : Any = {
    visit_Expression(the_node);
    null
  };

  override def visit_no_expr(the_node:Cno_expr) : Any = {
    visit_Expression(the_node);
    null
  };

  override def visit_variable(the_node:Cvariable,name:Symbol) : Any = {
    visit_Expression(the_node);
    null
  };
}
// Automatically generated.  Do not edit!
class CoolTreeModifier() extends CoolVisitor() {
  var line_number : Int = 0;
  def get_line_number() : Int = line_number;

  override def visit_Program(n:Program) : Program = {
    line_number = n.get_line_number();
    n.accept(this) match {
      case nn:Program => nn
    }
  };

  override def visit_Class(n:Class) : Class = {
    line_number = n.get_line_number();
    n.accept(this) match {
      case nn:Class => nn
    }
  };

  def visit_Classes(node:Classes) : Classes = {
    line_number = node.get_line_number();
    node match {
      case a:Classes_append => visit_Classes(a.get1()).concat(visit_Classes(a.get2()))
      case a:Classes_one => visit_Classes_one(a.get())
      case a:Classes_nil => a
    }
  };
  override def visit_Classes_one(node:Class) : Classes = {
    line_number = node.get_line_number();
    new Classes_one(visit_Class(node))
  };

  override def visit_Feature(n:Feature) : Feature = {
    line_number = n.get_line_number();
    n.accept(this) match {
      case nn:Feature => nn
    }
  };

  def visit_Features(node:Features) : Features = {
    line_number = node.get_line_number();
    node match {
      case a:Features_append => visit_Features(a.get1()).concat(visit_Features(a.get2()))
      case a:Features_one => visit_Features_one(a.get())
      case a:Features_nil => a
    }
  };
  override def visit_Features_one(node:Feature) : Features = {
    line_number = node.get_line_number();
    new Features_one(visit_Feature(node))
  };

  override def visit_Formal(n:Formal) : Formal = {
    line_number = n.get_line_number();
    n.accept(this) match {
      case nn:Formal => nn
    }
  };

  def visit_Formals(node:Formals) : Formals = {
    line_number = node.get_line_number();
    node match {
      case a:Formals_append => visit_Formals(a.get1()).concat(visit_Formals(a.get2()))
      case a:Formals_one => visit_Formals_one(a.get())
      case a:Formals_nil => a
    }
  };
  override def visit_Formals_one(node:Formal) : Formals = {
    line_number = node.get_line_number();
    new Formals_one(visit_Formal(node))
  };

  override def visit_Expression(n:Expression) : Expression = {
    line_number = n.get_line_number();
    n.accept(this) match {
      case nn:Expression => nn
    }
  };

  def visit_Expressions(node:Expressions) : Expressions = {
    line_number = node.get_line_number();
    node match {
      case a:Expressions_append => visit_Expressions(a.get1()).concat(visit_Expressions(a.get2()))
      case a:Expressions_one => visit_Expressions_one(a.get())
      case a:Expressions_nil => a
    }
  };
  override def visit_Expressions_one(node:Expression) : Expressions = {
    line_number = node.get_line_number();
    new Expressions_one(visit_Expression(node))
  };

  override def visit_Case(n:Case) : Case = {
    line_number = n.get_line_number();
    n.accept(this) match {
      case nn:Case => nn
    }
  };

  def visit_Cases(node:Cases) : Cases = {
    line_number = node.get_line_number();
    node match {
      case a:Cases_append => visit_Cases(a.get1()).concat(visit_Cases(a.get2()))
      case a:Cases_one => visit_Cases_one(a.get())
      case a:Cases_nil => a
    }
  };
  override def visit_Cases_one(node:Case) : Cases = {
    line_number = node.get_line_number();
    new Cases_one(visit_Case(node))
  };

  override def visit_program(the_node:Cprogram,classes:Classes) : Program = {
    the_node.set_classes(visit_Classes(classes));
    the_node
  };

  override def visit_class_decl(the_node:Cclass_decl,name:Symbol,parent:Symbol,features:Features,filename:Symbol) : Class = {
    the_node.set_features(visit_Features(features));
    the_node
  };

  override def visit_method(the_node:Cmethod,overridep:Boolean,name:Symbol,formals:Formals,return_type:Symbol,expr:Expression) : Feature = {
    the_node.set_formals(visit_Formals(formals));
    the_node.set_expr(visit_Expression(expr));
    the_node
  };

  override def visit_attr(the_node:Cattr,name:Symbol,of_type:Symbol) : Feature = {
    the_node
  };

  override def visit_formal(the_node:Cformal,name:Symbol,of_type:Symbol) : Formal = {
    the_node
  };

  override def visit_branch(the_node:Cbranch,name:Symbol,local_type:Symbol,expr:Expression) : Case = {
    the_node.set_expr(visit_Expression(expr));
    the_node
  };

  override def visit_assign(the_node:Cassign,name:Symbol,expr:Expression) : Expression = {
    the_node.set_expr(visit_Expression(expr));
    the_node
  };

  override def visit_static_dispatch(the_node:Cstatic_dispatch,expr:Expression,type_name:Symbol,name:Symbol,actuals:Expressions) : Expression = {
    the_node.set_expr(visit_Expression(expr));
    the_node.set_actuals(visit_Expressions(actuals));
    the_node
  };

  override def visit_dispatch(the_node:Cdispatch,expr:Expression,name:Symbol,actuals:Expressions) : Expression = {
    the_node.set_expr(visit_Expression(expr));
    the_node.set_actuals(visit_Expressions(actuals));
    the_node
  };

  override def visit_cond(the_node:Ccond,pred:Expression,then_exp:Expression,else_exp:Expression) : Expression = {
    the_node.set_pred(visit_Expression(pred));
    the_node.set_then_exp(visit_Expression(then_exp));
    the_node.set_else_exp(visit_Expression(else_exp));
    the_node
  };

  override def visit_loop(the_node:Cloop,pred:Expression,body:Expression) : Expression = {
    the_node.set_pred(visit_Expression(pred));
    the_node.set_body(visit_Expression(body));
    the_node
  };

  override def visit_typecase(the_node:Ctypecase,expr:Expression,cases:Cases) : Expression = {
    the_node.set_expr(visit_Expression(expr));
    the_node.set_cases(visit_Cases(cases));
    the_node
  };

  override def visit_block(the_node:Cblock,body:Expressions) : Expression = {
    the_node.set_body(visit_Expressions(body));
    the_node
  };

  override def visit_let(the_node:Clet,identifier:Symbol,local_type:Symbol,init:Expression,body:Expression) : Expression = {
    the_node.set_init(visit_Expression(init));
    the_node.set_body(visit_Expression(body));
    the_node
  };

  override def visit_add(the_node:Cadd,e1:Expression,e2:Expression) : Expression = {
    the_node.set_e1(visit_Expression(e1));
    the_node.set_e2(visit_Expression(e2));
    the_node
  };

  override def visit_sub(the_node:Csub,e1:Expression,e2:Expression) : Expression = {
    the_node.set_e1(visit_Expression(e1));
    the_node.set_e2(visit_Expression(e2));
    the_node
  };

  override def visit_mul(the_node:Cmul,e1:Expression,e2:Expression) : Expression = {
    the_node.set_e1(visit_Expression(e1));
    the_node.set_e2(visit_Expression(e2));
    the_node
  };

  override def visit_div(the_node:Cdiv,e1:Expression,e2:Expression) : Expression = {
    the_node.set_e1(visit_Expression(e1));
    the_node.set_e2(visit_Expression(e2));
    the_node
  };

  override def visit_neg(the_node:Cneg,e1:Expression) : Expression = {
    the_node.set_e1(visit_Expression(e1));
    the_node
  };

  override def visit_lt(the_node:Clt,e1:Expression,e2:Expression) : Expression = {
    the_node.set_e1(visit_Expression(e1));
    the_node.set_e2(visit_Expression(e2));
    the_node
  };

  override def visit_leq(the_node:Cleq,e1:Expression,e2:Expression) : Expression = {
    the_node.set_e1(visit_Expression(e1));
    the_node.set_e2(visit_Expression(e2));
    the_node
  };

  override def visit_comp(the_node:Ccomp,e1:Expression) : Expression = {
    the_node.set_e1(visit_Expression(e1));
    the_node
  };

  override def visit_int_lit(the_node:Cint_lit,token:Symbol) : Expression = {
    the_node
  };

  override def visit_bool_lit(the_node:Cbool_lit,value:Boolean) : Expression = {
    the_node
  };

  override def visit_string_lit(the_node:Cstring_lit,token:Symbol) : Expression = {
    the_node
  };

  override def visit_alloc(the_node:Calloc,type_name:Symbol) : Expression = {
    the_node
  };

  override def visit_nil(the_node:Cnil) : Expression = {
    the_node
  };

  override def visit_unit(the_node:Cunit) : Expression = {
    the_node
  };

  override def visit_no_expr(the_node:Cno_expr) : Expression = {
    the_node
  };

  override def visit_variable(the_node:Cvariable,name:Symbol) : Expression = {
    the_node
  };
}
// Automatically generated.  Do not edit!
class CoolTreeCopy(var factory : CoolNodeFactory) extends CoolVisitor() {
  var index : ArrayAny = new ArrayAny(100);

  def record_copy(n1 : CoolNode, n2 : CoolNode) : Unit = {
    n2.set_line_number(n1.get_line_number());
    var id : Int = n1.get_id();
    if (index.length() <= id) index = index.resize(id+1) else ();
    index.set(id,n2); ()
  };

  def finish() : Unit = {
    var i : Int = 0;
    var n : Int = index.length();
    while (i < n) {
      index.get(i) match {
        case null => ()
        case node:Program =>
          node.get_any_class() match {
            case null => ()
            case v:Class =>
              var j : Int = v.get_id();
              if (n <= j) () else {
                index.get(j) match {
                  case null => ()
                  case w:Class => node.set_any_class(w)
                }
              }
          };
          node.get_unit_class() match {
            case null => ()
            case v:Class =>
              var j : Int = v.get_id();
              if (n <= j) () else {
                index.get(j) match {
                  case null => ()
                  case w:Class => node.set_unit_class(w)
                }
              }
          };
          node.get_int_class() match {
            case null => ()
            case v:Class =>
              var j : Int = v.get_id();
              if (n <= j) () else {
                index.get(j) match {
                  case null => ()
                  case w:Class => node.set_int_class(w)
                }
              }
          };
          node.get_boolean_class() match {
            case null => ()
            case v:Class =>
              var j : Int = v.get_id();
              if (n <= j) () else {
                index.get(j) match {
                  case null => ()
                  case w:Class => node.set_boolean_class(w)
                }
              }
          };
          node.get_string_class() match {
            case null => ()
            case v:Class =>
              var j : Int = v.get_id();
              if (n <= j) () else {
                index.get(j) match {
                  case null => ()
                  case w:Class => node.set_string_class(w)
                }
              }
          };
          ()
        case node:Class =>
          node.get_superclass() match {
            case null => ()
            case v:Class =>
              var j : Int = v.get_id();
              if (n <= j) () else {
                index.get(j) match {
                  case null => ()
                  case w:Class => node.set_superclass(w)
                }
              }
          };
          ()
        case node:Feature =>
          node.get_owner() match {
            case null => ()
            case v:Cclass_decl =>
              var j : Int = v.get_id();
              if (n <= j) () else {
                index.get(j) match {
                  case null => ()
                  case w:Cclass_decl => node.set_owner(w)
                }
              }
          };
          node.get_overrides() match {
            case null => ()
            case v:Cmethod =>
              var j : Int = v.get_id();
              if (n <= j) () else {
                index.get(j) match {
                  case null => ()
                  case w:Cmethod => node.set_overrides(w)
                }
              }
          };
          node.get_feature_of_class() match {
            case null => ()
            case v:Class =>
              var j : Int = v.get_id();
              if (n <= j) () else {
                index.get(j) match {
                  case null => ()
                  case w:Class => node.set_feature_of_class(w)
                }
              }
          };
          ()
        case node:Formal =>
          node.get_formal_of_class() match {
            case null => ()
            case v:Class =>
              var j : Int = v.get_id();
              if (n <= j) () else {
                index.get(j) match {
                  case null => ()
                  case w:Class => node.set_formal_of_class(w)
                }
              }
          };
          ()
        case node:Expression =>
          node.get_of_class() match {
            case null => ()
            case v:Class =>
              var j : Int = v.get_id();
              if (n <= j) () else {
                index.get(j) match {
                  case null => ()
                  case w:Class => node.set_of_class(w)
                }
              }
          };
          node.get_binding() match {
            case null => ()
            case v:CoolNode =>
              var j : Int = v.get_id();
              if (n <= j) () else {
                index.get(j) match {
                  case null => ()
                  case w:CoolNode => node.set_binding(w)
                }
              }
          };
          node.get_mbinding() match {
            case null => ()
            case v:Cmethod =>
              var j : Int = v.get_id();
              if (n <= j) () else {
                index.get(j) match {
                  case null => ()
                  case w:Cmethod => node.set_mbinding(w)
                }
              }
          };
          ()
        case node:Case =>
          node.get_case_of_class() match {
            case null => ()
            case v:Class =>
              var j : Int = v.get_id();
              if (n <= j) () else {
                index.get(j) match {
                  case null => ()
                  case w:Class => node.set_case_of_class(w)
                }
              }
          };
          ()
        case n:CoolNode => n
      };
      i = i + 1
    }
  };


  override def visit_Program(n:Program) : Program = {
    n.accept(this) match {
      case nn:Program =>
        record_copy(n,nn);
        nn.set_any_class(n.get_any_class());
        nn.set_unit_class(n.get_unit_class());
        nn.set_int_class(n.get_int_class());
        nn.set_boolean_class(n.get_boolean_class());
        nn.set_string_class(n.get_string_class());
        nn
    }
  };

  override def visit_Class(n:Class) : Class = {
    n.accept(this) match {
      case nn:Class =>
        record_copy(n,nn);
        nn.set_superclass(n.get_superclass());
        nn.set_inheritablep(n.get_inheritablep());
        nn
    }
  };

  def visit_Classes(node:Classes) : Classes = {
    node match {
      case a:Classes_append => visit_Classes(a.get1()).concat(visit_Classes(a.get2()))
      case a:Classes_one => visit_Classes_one(a.get())
      case a:Classes_nil => a
    }
  };
  override def visit_Classes_one(node:Class) : Classes = {
    new Classes_one(visit_Class(node))
  };

  override def visit_Feature(n:Feature) : Feature = {
    n.accept(this) match {
      case nn:Feature =>
        record_copy(n,nn);
        nn.set_owner(n.get_owner());
        nn.set_overrides(n.get_overrides());
        nn.set_feature_of_class(n.get_feature_of_class());
        nn
    }
  };

  def visit_Features(node:Features) : Features = {
    node match {
      case a:Features_append => visit_Features(a.get1()).concat(visit_Features(a.get2()))
      case a:Features_one => visit_Features_one(a.get())
      case a:Features_nil => a
    }
  };
  override def visit_Features_one(node:Feature) : Features = {
    new Features_one(visit_Feature(node))
  };

  override def visit_Formal(n:Formal) : Formal = {
    n.accept(this) match {
      case nn:Formal =>
        record_copy(n,nn);
        nn.set_formal_of_class(n.get_formal_of_class());
        nn
    }
  };

  def visit_Formals(node:Formals) : Formals = {
    node match {
      case a:Formals_append => visit_Formals(a.get1()).concat(visit_Formals(a.get2()))
      case a:Formals_one => visit_Formals_one(a.get())
      case a:Formals_nil => a
    }
  };
  override def visit_Formals_one(node:Formal) : Formals = {
    new Formals_one(visit_Formal(node))
  };

  override def visit_Expression(n:Expression) : Expression = {
    n.accept(this) match {
      case nn:Expression =>
        record_copy(n,nn);
        nn.set_of_type(n.get_of_type());
        nn.set_of_class(n.get_of_class());
        nn.set_binding(n.get_binding());
        nn.set_mbinding(n.get_mbinding());
        nn
    }
  };

  def visit_Expressions(node:Expressions) : Expressions = {
    node match {
      case a:Expressions_append => visit_Expressions(a.get1()).concat(visit_Expressions(a.get2()))
      case a:Expressions_one => visit_Expressions_one(a.get())
      case a:Expressions_nil => a
    }
  };
  override def visit_Expressions_one(node:Expression) : Expressions = {
    new Expressions_one(visit_Expression(node))
  };

  override def visit_Case(n:Case) : Case = {
    n.accept(this) match {
      case nn:Case =>
        record_copy(n,nn);
        nn.set_case_of_type(n.get_case_of_type());
        nn.set_case_of_class(n.get_case_of_class());
        nn
    }
  };

  def visit_Cases(node:Cases) : Cases = {
    node match {
      case a:Cases_append => visit_Cases(a.get1()).concat(visit_Cases(a.get2()))
      case a:Cases_one => visit_Cases_one(a.get())
      case a:Cases_nil => a
    }
  };
  override def visit_Cases_one(node:Case) : Cases = {
    new Cases_one(visit_Case(node))
  };

  override def visit_program(the_node:Cprogram,classes:Classes) : Program = {
    var classes_ : Classes = visit_Classes(classes);
    factory.program(classes_)
  };

  override def visit_class_decl(the_node:Cclass_decl,name:Symbol,parent:Symbol,features:Features,filename:Symbol) : Class = {
    var name_ : Symbol = name;
    var parent_ : Symbol = parent;
    var features_ : Features = visit_Features(features);
    var filename_ : Symbol = filename;
    factory.class_decl(name_,parent_,features_,filename_)
  };

  override def visit_method(the_node:Cmethod,overridep:Boolean,name:Symbol,formals:Formals,return_type:Symbol,expr:Expression) : Feature = {
    var overridep_ : Boolean = overridep;
    var name_ : Symbol = name;
    var formals_ : Formals = visit_Formals(formals);
    var return_type_ : Symbol = return_type;
    var expr_ : Expression = visit_Expression(expr);
    factory.method(overridep_,name_,formals_,return_type_,expr_)
  };

  override def visit_attr(the_node:Cattr,name:Symbol,of_type:Symbol) : Feature = {
    var name_ : Symbol = name;
    var of_type_ : Symbol = of_type;
    factory.attr(name_,of_type_)
  };

  override def visit_formal(the_node:Cformal,name:Symbol,of_type:Symbol) : Formal = {
    var name_ : Symbol = name;
    var of_type_ : Symbol = of_type;
    factory.formal(name_,of_type_)
  };

  override def visit_branch(the_node:Cbranch,name:Symbol,local_type:Symbol,expr:Expression) : Case = {
    var name_ : Symbol = name;
    var local_type_ : Symbol = local_type;
    var expr_ : Expression = visit_Expression(expr);
    factory.branch(name_,local_type_,expr_)
  };

  override def visit_assign(the_node:Cassign,name:Symbol,expr:Expression) : Expression = {
    var name_ : Symbol = name;
    var expr_ : Expression = visit_Expression(expr);
    factory.assign(name_,expr_)
  };

  override def visit_static_dispatch(the_node:Cstatic_dispatch,expr:Expression,type_name:Symbol,name:Symbol,actuals:Expressions) : Expression = {
    var expr_ : Expression = visit_Expression(expr);
    var type_name_ : Symbol = type_name;
    var name_ : Symbol = name;
    var actuals_ : Expressions = visit_Expressions(actuals);
    factory.static_dispatch(expr_,type_name_,name_,actuals_)
  };

  override def visit_dispatch(the_node:Cdispatch,expr:Expression,name:Symbol,actuals:Expressions) : Expression = {
    var expr_ : Expression = visit_Expression(expr);
    var name_ : Symbol = name;
    var actuals_ : Expressions = visit_Expressions(actuals);
    factory.dispatch(expr_,name_,actuals_)
  };

  override def visit_cond(the_node:Ccond,pred:Expression,then_exp:Expression,else_exp:Expression) : Expression = {
    var pred_ : Expression = visit_Expression(pred);
    var then_exp_ : Expression = visit_Expression(then_exp);
    var else_exp_ : Expression = visit_Expression(else_exp);
    factory.cond(pred_,then_exp_,else_exp_)
  };

  override def visit_loop(the_node:Cloop,pred:Expression,body:Expression) : Expression = {
    var pred_ : Expression = visit_Expression(pred);
    var body_ : Expression = visit_Expression(body);
    factory.loop(pred_,body_)
  };

  override def visit_typecase(the_node:Ctypecase,expr:Expression,cases:Cases) : Expression = {
    var expr_ : Expression = visit_Expression(expr);
    var cases_ : Cases = visit_Cases(cases);
    factory.typecase(expr_,cases_)
  };

  override def visit_block(the_node:Cblock,body:Expressions) : Expression = {
    var body_ : Expressions = visit_Expressions(body);
    factory.block(body_)
  };

  override def visit_let(the_node:Clet,identifier:Symbol,local_type:Symbol,init:Expression,body:Expression) : Expression = {
    var identifier_ : Symbol = identifier;
    var local_type_ : Symbol = local_type;
    var init_ : Expression = visit_Expression(init);
    var body_ : Expression = visit_Expression(body);
    factory.let(identifier_,local_type_,init_,body_)
  };

  override def visit_add(the_node:Cadd,e1:Expression,e2:Expression) : Expression = {
    var e1_ : Expression = visit_Expression(e1);
    var e2_ : Expression = visit_Expression(e2);
    factory.add(e1_,e2_)
  };

  override def visit_sub(the_node:Csub,e1:Expression,e2:Expression) : Expression = {
    var e1_ : Expression = visit_Expression(e1);
    var e2_ : Expression = visit_Expression(e2);
    factory.sub(e1_,e2_)
  };

  override def visit_mul(the_node:Cmul,e1:Expression,e2:Expression) : Expression = {
    var e1_ : Expression = visit_Expression(e1);
    var e2_ : Expression = visit_Expression(e2);
    factory.mul(e1_,e2_)
  };

  override def visit_div(the_node:Cdiv,e1:Expression,e2:Expression) : Expression = {
    var e1_ : Expression = visit_Expression(e1);
    var e2_ : Expression = visit_Expression(e2);
    factory.div(e1_,e2_)
  };

  override def visit_neg(the_node:Cneg,e1:Expression) : Expression = {
    var e1_ : Expression = visit_Expression(e1);
    factory.neg(e1_)
  };

  override def visit_lt(the_node:Clt,e1:Expression,e2:Expression) : Expression = {
    var e1_ : Expression = visit_Expression(e1);
    var e2_ : Expression = visit_Expression(e2);
    factory.lt(e1_,e2_)
  };

  override def visit_leq(the_node:Cleq,e1:Expression,e2:Expression) : Expression = {
    var e1_ : Expression = visit_Expression(e1);
    var e2_ : Expression = visit_Expression(e2);
    factory.leq(e1_,e2_)
  };

  override def visit_comp(the_node:Ccomp,e1:Expression) : Expression = {
    var e1_ : Expression = visit_Expression(e1);
    factory.comp(e1_)
  };

  override def visit_int_lit(the_node:Cint_lit,token:Symbol) : Expression = {
    var token_ : Symbol = token;
    factory.int_lit(token_)
  };

  override def visit_bool_lit(the_node:Cbool_lit,value:Boolean) : Expression = {
    var value_ : Boolean = value;
    factory.bool_lit(value_)
  };

  override def visit_string_lit(the_node:Cstring_lit,token:Symbol) : Expression = {
    var token_ : Symbol = token;
    factory.string_lit(token_)
  };

  override def visit_alloc(the_node:Calloc,type_name:Symbol) : Expression = {
    var type_name_ : Symbol = type_name;
    factory.alloc(type_name_)
  };

  override def visit_nil(the_node:Cnil) : Expression = {
    factory.nil()
  };

  override def visit_unit(the_node:Cunit) : Expression = {
    factory.unit()
  };

  override def visit_no_expr(the_node:Cno_expr) : Expression = {
    factory.no_expr()
  };

  override def visit_variable(the_node:Cvariable,name:Symbol) : Expression = {
    var name_ : Symbol = name;
    factory.variable(name_)
  };
}
class CoolAbstractTreeDumper() extends CoolTreeVisitor() {
  var indent : Int = 0;

  def dump(n : CoolNode) : Any = {
    indent = 0;
    n.accept(this)
  };

  def out_indent() : Unit = {
    var i : Int = 0;
    while (i < indent) {
      out("  ");
      i = i + 1
    }
  };

  def out_attribute(label : String, value : String, default : String) : 
Any = {
    if (value == default) null
    else {
      out_indent();
      out(">");
      out(label);
      out(" = ");
      out(value);
      out("\n")
    }
  };

  def dump_Any(v : Any) : String = {
    if (is_null(v)) "null" else v.toString()
  };

  def dump_remote(v : CoolNode) : String = dump_Any(v);

  def dump_Symbol(v : Symbol) : String = dump_Any(v);

  def dump_Boolean(v : Boolean) : String = dump_Any(v);

  override def visit_Program(n : Program) : Any = {
    out_attribute("any_class",dump_remote(n.get_any_class()),any_class_default);
    out_attribute("unit_class",dump_remote(n.get_unit_class()),unit_class_default);
    out_attribute("int_class",dump_remote(n.get_int_class()),int_class_default);
    out_attribute("boolean_class",dump_remote(n.get_boolean_class()),boolean_class_default);
    out_attribute("string_class",dump_remote(n.get_string_class()),string_class_default);
    null
  };

  override def visit_Class(n : Class) : Any = {
    out_attribute("superclass",dump_remote(n.get_superclass()),superclass_default);
    out_attribute("inheritablep",dump_Boolean(n.get_inheritablep()),inheritablep_default);
    null
  };

  override def visit_Classes_one(e : Class) : Any = {
    indent = indent + 1;
    super.visit_Classes_one(e);
    indent = indent - 1
  };

  override def visit_Feature(n : Feature) : Any = {
    out_attribute("owner",dump_Cclass_decl(n.get_owner()),owner_default);
    out_attribute("overrides",dump_Cmethod(n.get_overrides()),overrides_default);
    out_attribute("feature_of_class",dump_remote(n.get_feature_of_class()),feature_of_class_default);
    null
  };

  override def visit_Features_one(e : Feature) : Any = {
    indent = indent + 1;
    super.visit_Features_one(e);
    indent = indent - 1
  };

  override def visit_Formal(n : Formal) : Any = {
    out_attribute("formal_of_class",dump_remote(n.get_formal_of_class()),formal_of_class_default);
    null
  };

  override def visit_Formals_one(e : Formal) : Any = {
    indent = indent + 1;
    super.visit_Formals_one(e);
    indent = indent - 1
  };

  override def visit_Expression(n : Expression) : Any = {
    out_attribute("of_type",dump_Symbol(n.get_of_type()),of_type_default);
    out_attribute("of_class",dump_remote(n.get_of_class()),of_class_default);
    out_attribute("binding",dump_CoolNode(n.get_binding()),binding_default);
    out_attribute("mbinding",dump_Cmethod(n.get_mbinding()),mbinding_default);
    null
  };

  override def visit_Expressions_one(e : Expression) : Any = {
    indent = indent + 1;
    super.visit_Expressions_one(e);
    indent = indent - 1
  };

  override def visit_Case(n : Case) : Any = {
    out_attribute("case_of_type",dump_Symbol(n.get_case_of_type()),case_of_type_default);
    out_attribute("case_of_class",dump_remote(n.get_case_of_class()),case_of_class_default);
    null
  };

  override def visit_Cases_one(e : Case) : Any = {
    indent = indent + 1;
    super.visit_Cases_one(e);
    indent = indent - 1
  };

  override def visit_program(the_node:Cprogram,classes:Classes) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = program:");
    out(the_node.get_line_number().toString()).out(" ");
    out("\n");
    super.visit_program(the_node,classes);
    indent = indent - 1
  };

  override def visit_class_decl(the_node:Cclass_decl,name:Symbol,parent:Symbol,features:Features,filename:Symbol) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = class_decl:");
    out(the_node.get_line_number().toString()).out(" ");
    out(dump_Symbol(name)).out(" ");
    out(dump_Symbol(parent)).out(" ");
    out(dump_Symbol(filename)).out(" ");
    out("\n");
    super.visit_class_decl(the_node,name,parent,features,filename);
    indent = indent - 1
  };

  override def visit_method(the_node:Cmethod,overridep:Boolean,name:Symbol,formals:Formals,return_type:Symbol,expr:Expression) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = method:");
    out(the_node.get_line_number().toString()).out(" ");
    out(dump_Boolean(overridep)).out(" ");
    out(dump_Symbol(name)).out(" ");
    out(dump_Symbol(return_type)).out(" ");
    out("\n");
    super.visit_method(the_node,overridep,name,formals,return_type,expr);
    indent = indent - 1
  };

  override def visit_attr(the_node:Cattr,name:Symbol,of_type:Symbol) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = attr:");
    out(the_node.get_line_number().toString()).out(" ");
    out(dump_Symbol(name)).out(" ");
    out(dump_Symbol(of_type)).out(" ");
    out("\n");
    super.visit_attr(the_node,name,of_type);
    indent = indent - 1
  };

  override def visit_formal(the_node:Cformal,name:Symbol,of_type:Symbol) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = formal:");
    out(the_node.get_line_number().toString()).out(" ");
    out(dump_Symbol(name)).out(" ");
    out(dump_Symbol(of_type)).out(" ");
    out("\n");
    super.visit_formal(the_node,name,of_type);
    indent = indent - 1
  };

  override def visit_branch(the_node:Cbranch,name:Symbol,local_type:Symbol,expr:Expression) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = branch:");
    out(the_node.get_line_number().toString()).out(" ");
    out(dump_Symbol(name)).out(" ");
    out(dump_Symbol(local_type)).out(" ");
    out("\n");
    super.visit_branch(the_node,name,local_type,expr);
    indent = indent - 1
  };

  override def visit_assign(the_node:Cassign,name:Symbol,expr:Expression) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = assign:");
    out(the_node.get_line_number().toString()).out(" ");
    out(dump_Symbol(name)).out(" ");
    out("\n");
    super.visit_assign(the_node,name,expr);
    indent = indent - 1
  };

  override def visit_static_dispatch(the_node:Cstatic_dispatch,expr:Expression,type_name:Symbol,name:Symbol,actuals:Expressions) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = static_dispatch:");
    out(the_node.get_line_number().toString()).out(" ");
    out(dump_Symbol(type_name)).out(" ");
    out(dump_Symbol(name)).out(" ");
    out("\n");
    super.visit_static_dispatch(the_node,expr,type_name,name,actuals);
    indent = indent - 1
  };

  override def visit_dispatch(the_node:Cdispatch,expr:Expression,name:Symbol,actuals:Expressions) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = dispatch:");
    out(the_node.get_line_number().toString()).out(" ");
    out(dump_Symbol(name)).out(" ");
    out("\n");
    super.visit_dispatch(the_node,expr,name,actuals);
    indent = indent - 1
  };

  override def visit_cond(the_node:Ccond,pred:Expression,then_exp:Expression,else_exp:Expression) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = cond:");
    out(the_node.get_line_number().toString()).out(" ");
    out("\n");
    super.visit_cond(the_node,pred,then_exp,else_exp);
    indent = indent - 1
  };

  override def visit_loop(the_node:Cloop,pred:Expression,body:Expression) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = loop:");
    out(the_node.get_line_number().toString()).out(" ");
    out("\n");
    super.visit_loop(the_node,pred,body);
    indent = indent - 1
  };

  override def visit_typecase(the_node:Ctypecase,expr:Expression,cases:Cases) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = typecase:");
    out(the_node.get_line_number().toString()).out(" ");
    out("\n");
    super.visit_typecase(the_node,expr,cases);
    indent = indent - 1
  };

  override def visit_block(the_node:Cblock,body:Expressions) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = block:");
    out(the_node.get_line_number().toString()).out(" ");
    out("\n");
    super.visit_block(the_node,body);
    indent = indent - 1
  };

  override def visit_let(the_node:Clet,identifier:Symbol,local_type:Symbol,init:Expression,body:Expression) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = let:");
    out(the_node.get_line_number().toString()).out(" ");
    out(dump_Symbol(identifier)).out(" ");
    out(dump_Symbol(local_type)).out(" ");
    out("\n");
    super.visit_let(the_node,identifier,local_type,init,body);
    indent = indent - 1
  };

  override def visit_add(the_node:Cadd,e1:Expression,e2:Expression) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = add:");
    out(the_node.get_line_number().toString()).out(" ");
    out("\n");
    super.visit_add(the_node,e1,e2);
    indent = indent - 1
  };

  override def visit_sub(the_node:Csub,e1:Expression,e2:Expression) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = sub:");
    out(the_node.get_line_number().toString()).out(" ");
    out("\n");
    super.visit_sub(the_node,e1,e2);
    indent = indent - 1
  };

  override def visit_mul(the_node:Cmul,e1:Expression,e2:Expression) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = mul:");
    out(the_node.get_line_number().toString()).out(" ");
    out("\n");
    super.visit_mul(the_node,e1,e2);
    indent = indent - 1
  };

  override def visit_div(the_node:Cdiv,e1:Expression,e2:Expression) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = div:");
    out(the_node.get_line_number().toString()).out(" ");
    out("\n");
    super.visit_div(the_node,e1,e2);
    indent = indent - 1
  };

  override def visit_neg(the_node:Cneg,e1:Expression) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = neg:");
    out(the_node.get_line_number().toString()).out(" ");
    out("\n");
    super.visit_neg(the_node,e1);
    indent = indent - 1
  };

  override def visit_lt(the_node:Clt,e1:Expression,e2:Expression) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = lt:");
    out(the_node.get_line_number().toString()).out(" ");
    out("\n");
    super.visit_lt(the_node,e1,e2);
    indent = indent - 1
  };

  override def visit_leq(the_node:Cleq,e1:Expression,e2:Expression) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = leq:");
    out(the_node.get_line_number().toString()).out(" ");
    out("\n");
    super.visit_leq(the_node,e1,e2);
    indent = indent - 1
  };

  override def visit_comp(the_node:Ccomp,e1:Expression) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = comp:");
    out(the_node.get_line_number().toString()).out(" ");
    out("\n");
    super.visit_comp(the_node,e1);
    indent = indent - 1
  };

  override def visit_int_lit(the_node:Cint_lit,token:Symbol) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = int_lit:");
    out(the_node.get_line_number().toString()).out(" ");
    out(dump_Symbol(token)).out(" ");
    out("\n");
    super.visit_int_lit(the_node,token);
    indent = indent - 1
  };

  override def visit_bool_lit(the_node:Cbool_lit,value:Boolean) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = bool_lit:");
    out(the_node.get_line_number().toString()).out(" ");
    out(dump_Boolean(value)).out(" ");
    out("\n");
    super.visit_bool_lit(the_node,value);
    indent = indent - 1
  };

  override def visit_string_lit(the_node:Cstring_lit,token:Symbol) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = string_lit:");
    out(the_node.get_line_number().toString()).out(" ");
    out(dump_Symbol(token)).out(" ");
    out("\n");
    super.visit_string_lit(the_node,token);
    indent = indent - 1
  };

  override def visit_alloc(the_node:Calloc,type_name:Symbol) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = alloc:");
    out(the_node.get_line_number().toString()).out(" ");
    out(dump_Symbol(type_name)).out(" ");
    out("\n");
    super.visit_alloc(the_node,type_name);
    indent = indent - 1
  };

  override def visit_nil(the_node:Cnil) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = nil:");
    out(the_node.get_line_number().toString()).out(" ");
    out("\n");
    super.visit_nil(the_node);
    indent = indent - 1
  };

  override def visit_unit(the_node:Cunit) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = unit:");
    out(the_node.get_line_number().toString()).out(" ");
    out("\n");
    super.visit_unit(the_node);
    indent = indent - 1
  };

  override def visit_no_expr(the_node:Cno_expr) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = no_expr:");
    out(the_node.get_line_number().toString()).out(" ");
    out("\n");
    super.visit_no_expr(the_node);
    indent = indent - 1
  };

  override def visit_variable(the_node:Cvariable,name:Symbol) : Any = {
    out_indent();
    indent = indent + 1;
    out("@").out(the_node.get_id().toString()).out(" = variable:");
    out(the_node.get_line_number().toString()).out(" ");
    out(dump_Symbol(name)).out(" ");
    out("\n");
    super.visit_variable(the_node,name);
    indent = indent - 1
  };

  def dump_CoolNode(v : CoolNode) : String = dump_Any(v);

  def dump_Cmethod(v : Cmethod) : String = dump_Any(v);

  def dump_Cclass_decl(v : Cclass_decl) : String = dump_Any(v);

  var any_class_default : String = dump_remote(null);

  var unit_class_default : String = dump_remote(null);

  var int_class_default : String = dump_remote(null);

  var boolean_class_default : String = dump_remote(null);

  var string_class_default : String = dump_remote(null);

  var superclass_default : String = dump_remote(null);

  var inheritablep_default : String = dump_Boolean(false);

  var owner_default : String = dump_Cclass_decl(null);

  var overrides_default : String = dump_Cmethod(null);

  var feature_of_class_default : String = dump_remote(null);

  var formal_of_class_default : String = dump_remote(null);

  var case_of_type_default : String = dump_Symbol(null);

  var case_of_class_default : String = dump_remote(null);

  var of_type_default : String = dump_Symbol(null);

  var of_class_default : String = dump_remote(null);

  var binding_default : String = dump_CoolNode(null);

  var mbinding_default : String = dump_Cmethod(null);
}
class CoolTreeParserAttribute(var node : CoolNode, var name : String, var value : String) 
{
  def get_node() : CoolNode = node;
  def get_name() : String = name;
  def get_value() : String = value;

  def set_node(n : CoolNode) : Unit = node = n;
}

class CoolAbstractTreeParser() extends IO() {
  var all_nodes : ArrayAny = new ArrayAny(10);

  def set(i : Int, n : CoolNode) : Unit = {
    while (all_nodes.length() <= i) {
      all_nodes = all_nodes.resize(all_nodes.length()*2)
    };
    all_nodes.set(i,n);
    ()
  };

  def get(i : Int) : CoolNode = all_nodes.get(i) match {
    case n:CoolNode => n
  };

  var all_attrs : ArrayAny = new ArrayAny(10);
  var num_attrs : Int = 0;

  var converter : A2I = new A2I();

  def add(a : CoolTreeParserAttribute) : Unit = {
    while (all_attrs.length() <= num_attrs) {
      all_attrs = all_attrs.resize(all_attrs.length()*2)
    };
    all_attrs.set(num_attrs,a);
    num_attrs = num_attrs + 1
  };

  var current : String = null;
  var current_in : Int = 0;
  var current_id : Int = 0;
  var current_name : String = "";
  var current_lno : Int = 0;
  var current_vals : String = "";

  var max_id : Int = 0;
  def get_max_id() : Int = max_id;

  def read_next_line() : Unit = {
    var i : Int = 0;
    current = in();
    if (is_null(current)) {
      current = "X"
    } else ();
    while (current.charAt(i) == 32) i = i + 1;
    current_in = i;
    current = current.substring(i,current.length())
  };

  def start() : Unit = read_next_line();

  def check_indent(indent : Int) : Unit =
    if (indent == current_in) ()
    else abort("indentation wrong");

  def split_node_line() : Unit = {
    var st : String = current;
    var sep : Int = st.indexOf(" ");
    current_id = converter.a2i(st.substring(1,sep));
    if (max_id < current_id) max_id = current_id else ();
    st = st.substring(sep+3,st.length());
    var col : Int = st.indexOf(":");
    current_name = st.substring(0,col);
    sep = st.indexOf(" ");
    current_lno = converter.a2i(st.substring(col+1,sep));
    current_vals = st.substring(sep+1,st.length())
  };

  def next_value() : String = {
    var sep : Int = current_vals.indexOf(" ");
    var result : String = current_vals.substring(0,sep);
    current_vals = current_vals.substring(sep+1,current_vals.length());
    result
  };

  def set_node_numbers(node : CoolNode, id : Int, lno : Int) : Unit = {
    node.set_id(id);
    node.set_line_number(lno);
    set(id,node)
  };

  def handle_attr_line() : Unit = {
    var st : String = current;
    var sep : Int = st.indexOf(" ");
    var name : String = current.substring(1,sep);
    var value : String = current.substring(sep+3,st.length());
    add(new CoolTreeParserAttribute(null,name,value))
  };

  def read_attributes() : Unit = {
    read_next_line();
    while (current.charAt(0) == 62) {
      handle_attr_line();
      read_next_line()
    }
  };

  def allocate_attrs(before : Int, after : Int, node : CoolNode) : Unit = {
    var i : Int = before;
    while (i < after) {
      all_attrs.get(i) match {
	case a:CoolTreeParserAttribute =>
	  a.set_node(node)
      };
      i = i + 1
    }
  };

  def resolve_attributes() : Unit = {
    var i : Int = 0;
    while (i < num_attrs) {
      all_attrs.get(i) match {
	case a:CoolTreeParserAttribute =>
	  resolve_attr(a.get_node(),a.get_name(),a.get_value())
      };
      i = i + 1
    }
  };

  def parse_remote(s : String) : CoolNode = {
    all_nodes.get(converter.a2i(s.substring(1,s.length()))) match {
      case n:CoolNode => n
    }
  };

  def parse_Symbol(s : String) : Symbol = abort("abstract parse_Symbol");

  def parse_Boolean(s : String) : Boolean = abort("abstract parse_Boolean");

  def parse_Classes(pindent : Int) : Classes = {
    var indent : Int = pindent + 2;
    var result : Classes = new Classes_nil();
    while (current_in == indent) {
      result = result.addcopy(parse_Class(indent))
    };
    result
  };

  def parse_Features(pindent : Int) : Features = {
    var indent : Int = pindent + 2;
    var result : Features = new Features_nil();
    while (current_in == indent) {
      result = result.addcopy(parse_Feature(indent))
    };
    result
  };

  def parse_Formals(pindent : Int) : Formals = {
    var indent : Int = pindent + 2;
    var result : Formals = new Formals_nil();
    while (current_in == indent) {
      result = result.addcopy(parse_Formal(indent))
    };
    result
  };

  def parse_Expressions(pindent : Int) : Expressions = {
    var indent : Int = pindent + 2;
    var result : Expressions = new Expressions_nil();
    while (current_in == indent) {
      result = result.addcopy(parse_Expression(indent))
    };
    result
  };

  def parse_Cases(pindent : Int) : Cases = {
    var indent : Int = pindent + 2;
    var result : Cases = new Cases_nil();
    while (current_in == indent) {
      result = result.addcopy(parse_Case(indent))
    };
    result
  };

  def parse_Program(indent : Int) : Program = {
    check_indent(indent);
    split_node_line();
    var id : Int = current_id;
    var lno : Int = current_lno;
    var before : Int = num_attrs;
    var after : Int = before;
    var node : Program =
      if (current_name == "program") {
        read_attributes();
        after = num_attrs;
        var classes : Classes = parse_Classes(indent+2);
        new Cprogram(classes)
      } else abort(current_name.concat(" is not a Program"));
    allocate_attrs(before,after,node);
    set_node_numbers(node,id,lno);
    node
  };

  def parse_Class(indent : Int) : Class = {
    check_indent(indent);
    split_node_line();
    var id : Int = current_id;
    var lno : Int = current_lno;
    var before : Int = num_attrs;
    var after : Int = before;
    var node : Class =
      if (current_name == "class_decl") {
        var name : Symbol = parse_Symbol(next_value());
        var parent : Symbol = parse_Symbol(next_value());
        var filename : Symbol = parse_Symbol(next_value());
        read_attributes();
        after = num_attrs;
        var features : Features = parse_Features(indent+2);
        new Cclass_decl(name,parent,features,filename)
      } else abort(current_name.concat(" is not a Class"));
    allocate_attrs(before,after,node);
    set_node_numbers(node,id,lno);
    node
  };

  def parse_Feature(indent : Int) : Feature = {
    check_indent(indent);
    split_node_line();
    var id : Int = current_id;
    var lno : Int = current_lno;
    var before : Int = num_attrs;
    var after : Int = before;
    var node : Feature =
      if (current_name == "method") {
        var overridep : Boolean = parse_Boolean(next_value());
        var name : Symbol = parse_Symbol(next_value());
        var return_type : Symbol = parse_Symbol(next_value());
        read_attributes();
        after = num_attrs;
        var formals : Formals = parse_Formals(indent+2);
        var expr : Expression = parse_Expression(indent+2);
        new Cmethod(overridep,name,formals,return_type,expr)
      } else if (current_name == "attr") {
        var name : Symbol = parse_Symbol(next_value());
        var of_type : Symbol = parse_Symbol(next_value());
        read_attributes();
        after = num_attrs;
        new Cattr(name,of_type)
      } else abort(current_name.concat(" is not a Feature"));
    allocate_attrs(before,after,node);
    set_node_numbers(node,id,lno);
    node
  };

  def parse_Formal(indent : Int) : Formal = {
    check_indent(indent);
    split_node_line();
    var id : Int = current_id;
    var lno : Int = current_lno;
    var before : Int = num_attrs;
    var after : Int = before;
    var node : Formal =
      if (current_name == "formal") {
        var name : Symbol = parse_Symbol(next_value());
        var of_type : Symbol = parse_Symbol(next_value());
        read_attributes();
        after = num_attrs;
        new Cformal(name,of_type)
      } else abort(current_name.concat(" is not a Formal"));
    allocate_attrs(before,after,node);
    set_node_numbers(node,id,lno);
    node
  };

  def parse_Case(indent : Int) : Case = {
    check_indent(indent);
    split_node_line();
    var id : Int = current_id;
    var lno : Int = current_lno;
    var before : Int = num_attrs;
    var after : Int = before;
    var node : Case =
      if (current_name == "branch") {
        var name : Symbol = parse_Symbol(next_value());
        var local_type : Symbol = parse_Symbol(next_value());
        read_attributes();
        after = num_attrs;
        var expr : Expression = parse_Expression(indent+2);
        new Cbranch(name,local_type,expr)
      } else abort(current_name.concat(" is not a Case"));
    allocate_attrs(before,after,node);
    set_node_numbers(node,id,lno);
    node
  };

  def parse_Expression(indent : Int) : Expression = {
    check_indent(indent);
    split_node_line();
    var id : Int = current_id;
    var lno : Int = current_lno;
    var before : Int = num_attrs;
    var after : Int = before;
    var node : Expression =
      if (current_name == "assign") {
        var name : Symbol = parse_Symbol(next_value());
        read_attributes();
        after = num_attrs;
        var expr : Expression = parse_Expression(indent+2);
        new Cassign(name,expr)
      } else if (current_name == "static_dispatch") {
        var type_name : Symbol = parse_Symbol(next_value());
        var name : Symbol = parse_Symbol(next_value());
        read_attributes();
        after = num_attrs;
        var expr : Expression = parse_Expression(indent+2);
        var actuals : Expressions = parse_Expressions(indent+2);
        new Cstatic_dispatch(expr,type_name,name,actuals)
      } else if (current_name == "dispatch") {
        var name : Symbol = parse_Symbol(next_value());
        read_attributes();
        after = num_attrs;
        var expr : Expression = parse_Expression(indent+2);
        var actuals : Expressions = parse_Expressions(indent+2);
        new Cdispatch(expr,name,actuals)
      } else if (current_name == "cond") {
        read_attributes();
        after = num_attrs;
        var pred : Expression = parse_Expression(indent+2);
        var then_exp : Expression = parse_Expression(indent+2);
        var else_exp : Expression = parse_Expression(indent+2);
        new Ccond(pred,then_exp,else_exp)
      } else if (current_name == "loop") {
        read_attributes();
        after = num_attrs;
        var pred : Expression = parse_Expression(indent+2);
        var body : Expression = parse_Expression(indent+2);
        new Cloop(pred,body)
      } else if (current_name == "typecase") {
        read_attributes();
        after = num_attrs;
        var expr : Expression = parse_Expression(indent+2);
        var cases : Cases = parse_Cases(indent+2);
        new Ctypecase(expr,cases)
      } else if (current_name == "block") {
        read_attributes();
        after = num_attrs;
        var body : Expressions = parse_Expressions(indent+2);
        new Cblock(body)
      } else if (current_name == "let") {
        var identifier : Symbol = parse_Symbol(next_value());
        var local_type : Symbol = parse_Symbol(next_value());
        read_attributes();
        after = num_attrs;
        var init : Expression = parse_Expression(indent+2);
        var body : Expression = parse_Expression(indent+2);
        new Clet(identifier,local_type,init,body)
      } else if (current_name == "add") {
        read_attributes();
        after = num_attrs;
        var e1 : Expression = parse_Expression(indent+2);
        var e2 : Expression = parse_Expression(indent+2);
        new Cadd(e1,e2)
      } else if (current_name == "sub") {
        read_attributes();
        after = num_attrs;
        var e1 : Expression = parse_Expression(indent+2);
        var e2 : Expression = parse_Expression(indent+2);
        new Csub(e1,e2)
      } else if (current_name == "mul") {
        read_attributes();
        after = num_attrs;
        var e1 : Expression = parse_Expression(indent+2);
        var e2 : Expression = parse_Expression(indent+2);
        new Cmul(e1,e2)
      } else if (current_name == "div") {
        read_attributes();
        after = num_attrs;
        var e1 : Expression = parse_Expression(indent+2);
        var e2 : Expression = parse_Expression(indent+2);
        new Cdiv(e1,e2)
      } else if (current_name == "neg") {
        read_attributes();
        after = num_attrs;
        var e1 : Expression = parse_Expression(indent+2);
        new Cneg(e1)
      } else if (current_name == "lt") {
        read_attributes();
        after = num_attrs;
        var e1 : Expression = parse_Expression(indent+2);
        var e2 : Expression = parse_Expression(indent+2);
        new Clt(e1,e2)
      } else if (current_name == "leq") {
        read_attributes();
        after = num_attrs;
        var e1 : Expression = parse_Expression(indent+2);
        var e2 : Expression = parse_Expression(indent+2);
        new Cleq(e1,e2)
      } else if (current_name == "comp") {
        read_attributes();
        after = num_attrs;
        var e1 : Expression = parse_Expression(indent+2);
        new Ccomp(e1)
      } else if (current_name == "int_lit") {
        var token : Symbol = parse_Symbol(next_value());
        read_attributes();
        after = num_attrs;
        new Cint_lit(token)
      } else if (current_name == "bool_lit") {
        var value : Boolean = parse_Boolean(next_value());
        read_attributes();
        after = num_attrs;
        new Cbool_lit(value)
      } else if (current_name == "string_lit") {
        var token : Symbol = parse_Symbol(next_value());
        read_attributes();
        after = num_attrs;
        new Cstring_lit(token)
      } else if (current_name == "alloc") {
        var type_name : Symbol = parse_Symbol(next_value());
        read_attributes();
        after = num_attrs;
        new Calloc(type_name)
      } else if (current_name == "nil") {
        read_attributes();
        after = num_attrs;
        new Cnil()
      } else if (current_name == "unit") {
        read_attributes();
        after = num_attrs;
        new Cunit()
      } else if (current_name == "no_expr") {
        read_attributes();
        after = num_attrs;
        new Cno_expr()
      } else if (current_name == "variable") {
        var name : Symbol = parse_Symbol(next_value());
        read_attributes();
        after = num_attrs;
        new Cvariable(name)
      } else abort(current_name.concat(" is not a Expression"));
    allocate_attrs(before,after,node);
    set_node_numbers(node,id,lno);
    node
  };

  def parse_CoolNode(s : String) : CoolNode = abort("abstract parse_CoolNode");

  def parse_Cmethod(s : String) : Cmethod = abort("abstract parse_Cmethod");

  def parse_Cclass_decl(s : String) : Cclass_decl = abort("abstract parse_Cclass_decl");

  def resolve_attr(node:CoolNode,name:String,value:String) : Unit =
    node match {
      case n:Program =>
        if (name == "any_class") parse_remote(value) match {
          case m:Class => n.set_any_class(m) }
        else if (name == "unit_class") parse_remote(value) match {
          case m:Class => n.set_unit_class(m) }
        else if (name == "int_class") parse_remote(value) match {
          case m:Class => n.set_int_class(m) }
        else if (name == "boolean_class") parse_remote(value) match {
          case m:Class => n.set_boolean_class(m) }
        else if (name == "string_class") parse_remote(value) match {
          case m:Class => n.set_string_class(m) }
        else abort("unknown attribute: ".concat(name))
      case n:Class =>
        if (name == "superclass") parse_remote(value) match {
          case m:Class => n.set_superclass(m) }
        else if (name == "inheritablep") n.set_inheritablep(parse_Boolean(value))
        else abort("unknown attribute: ".concat(name))
      case n:Feature =>
        if (name == "owner") n.set_owner(parse_Cclass_decl(value))
        else if (name == "overrides") n.set_overrides(parse_Cmethod(value))
        else if (name == "feature_of_class") parse_remote(value) match {
          case m:Class => n.set_feature_of_class(m) }
        else abort("unknown attribute: ".concat(name))
      case n:Formal =>
        if (name == "formal_of_class") parse_remote(value) match {
          case m:Class => n.set_formal_of_class(m) }
        else abort("unknown attribute: ".concat(name))
      case n:Case =>
        if (name == "case_of_type") n.set_case_of_type(parse_Symbol(value))
        else if (name == "case_of_class") parse_remote(value) match {
          case m:Class => n.set_case_of_class(m) }
        else abort("unknown attribute: ".concat(name))
      case n:Expression =>
        if (name == "of_type") n.set_of_type(parse_Symbol(value))
        else if (name == "of_class") parse_remote(value) match {
          case m:Class => n.set_of_class(m) }
        else if (name == "binding") n.set_binding(parse_CoolNode(value))
        else if (name == "mbinding") n.set_mbinding(parse_Cmethod(value))
        else abort("unknown attribute: ".concat(name))
    };
}
class CoolTreeParser() extends CoolAbstractTreeParser()
{
  def parse_String(s : String) : String = {
    var sb : StringBuilder = new StringBuilder();
    var i : Int = 0;
    var n : Int = s.length();
    var mark : Int = 0;
    while (i < n) {
      var ch : Int = s.charAt(i);
      var add : String = null;
      if (ch == 92) {
	ch = s.charAt(i+1);
	if (ch == 48) add = "\0"
	else if (ch == 92) add = "\\"
	else if (ch == 115) add = " "
	else if (ch == 110) add = "\n"
	else if (ch == 114) add = "\r"
	else abort("Unknown dump escape \\".concat(s))
      } else ();
      if (is_null(add)) ()
      else {
	sb.append(s.substring(mark,i));
	sb.append(add);
	i = i + 1;
	mark = i + 1
      };
      i = i + 1
    };
    sb.append(s.substring(mark,i));
    sb.toString()
  };

  override def parse_Symbol(s : String) : Symbol =
    if (s == "null") null
    else symbol(parse_String(s.substring(1,s.length())));

  override def parse_Boolean(s : String) : Boolean =
    if (s == "true") true
    else if (s == "false") false
    else abort("Not a Boolean: ".concat(s));

  override def parse_CoolNode(s : String) : CoolNode = parse_remote(s);

  override def parse_Cmethod(s : String) : Cmethod = parse_remote(s) match {
    case m:Cmethod => m
  };

  override def parse_Cclass_decl(s : String) : Cclass_decl = 
    parse_remote(s) match {
      case cd:Cclass_decl => cd
    };
}

class CoolTreeDumper() extends CoolAbstractTreeDumper()
{
  def dump_String(s : String) : String = {
    var sb : StringBuilder = new StringBuilder();
    var i : Int = 0;
    var n : Int = s.length();
    var mark : Int = 0;
    while (i < n) {
      var ch : Int = s.charAt(i);
      var add : String = null;
      if (ch == 0) add = "\\0"
      else if (ch == 13) add = "\\r"
      else if (ch == 32) add = "\\s"
      else if (ch == 10) add = "\\n"
      else if (ch == 92) add = "\\\\"
      else ();
      if (is_null(add)) ()
      else {
	sb.append(s.substring(mark,i));
	sb.append(add);
	mark = i + 1
      };
      i = i + 1
    };
    sb.append(s.substring(mark,i));
    sb.toString()
  };

  override def dump_Symbol(s : Symbol) : String = {
    if (is_null(s)) "null"
    else "'".concat(dump_String(symbol_name(s)))
  };
}
class CoolOptions()
{
  // Boolean flags

  var scan_debug : Boolean = false;
  def get_scan_debug() : Boolean = scan_debug;
  def set_scan_debug(f : Boolean) : Unit = scan_debug = f;

  var parse_debug : Boolean = false;
  def get_parse_debug() : Boolean = parse_debug;
  def set_parse_debug(f : Boolean) : Unit = parse_debug = f;

  var semant_debug : Boolean = false;
  def get_semant_debug() : Boolean = semant_debug;
  def set_semant_debug(f : Boolean) : Unit = semant_debug = f;

  var analysis_debug : Boolean = false;
  def get_analysis_debug() : Boolean = analysis_debug;
  def set_analysis_debug(f : Boolean) : Unit = analysis_debug = f;

  var cgen_debug : Boolean = false;
  def get_cgen_debug() : Boolean = cgen_debug;
  def set_cgen_debug(f : Boolean) : Unit = cgen_debug = f;

  var scan : Boolean = false;
  def get_scan() : Boolean = scan;
  def set_scan(f : Boolean) : Unit = scan = f;

  var parse : Boolean = true;
  def get_parse() : Boolean = parse;
  def set_parse(f : Boolean) : Unit = parse = f;

  var semant : Boolean = true;
  def get_semant() : Boolean = semant;
  def set_semant(f : Boolean) : Unit = semant = f;

  var analyze : Boolean = false;
  def get_analyze() : Boolean = analyze;
  def set_analyze(f : Boolean) : Unit = analyze = f;

  var optimize : Boolean = false;
  def get_optimize() : Boolean = optimize;
  def set_optimize(f : Boolean) : Unit = optimize = f;

  var codegen : Boolean = true;
  def get_codegen() : Boolean = codegen;
  def set_codegen(f : Boolean) : Unit = codegen = f;

  var enable_gc : Boolean = false;
  def get_enable_gc() : Boolean = enable_gc;
  def set_enable_gc(f : Boolean) : Unit = enable_gc = f;

  var right_to_left_children : Boolean = false;
  def get_right_to_left_children() : Boolean = right_to_left_children;
  def set_right_to_left_children(f : Boolean) : Unit = right_to_left_children = f;

  // String flags

  var basic_file:String = "/afs/cs.uwm.edu/users/classes/cs854/lib/basic.cool";
  def get_basic_file() : String = basic_file;
  def set_basic_file(f : String) : Unit = basic_file = f;

  var analysis : String = "resolve:inline:dead-let";
  def get_analysis() : String = analysis;
  def set_analysis(f : String) : Unit = analysis = f;

  var out_filename : String = null;
  def get_out_filename() : String = out_filename;
  def set_out_filename(f : String) : Unit = out_filename = f;


  // Int flags

  var max_errors : Int = 50;
  def get_max_errors() : Int = max_errors;
  def set_max_errors(f : Int) : Unit = max_errors = f;

  var strip_attributes : Int = 0;
  def get_strip_attributes() : Int = strip_attributes;
  def set_strip_attributes(f : Int) : Unit = strip_attributes = f;
}
class CheckSemant() extends CoolTreeVisitor()
{
  var native_sym : Symbol = symbol("native");
  var null_sym : Symbol = symbol("Null");
  var nothing_sym : Symbol = symbol("Nothing");

  override def visit_Program(n:Program) : Any = {
    check_non_null(n,"any_class",n.get_any_class());
    check_non_null(n,"int_class",n.get_int_class());
    check_non_null(n,"unit_class",n.get_unit_class());
    check_non_null(n,"boolean_class",n.get_boolean_class());
    check_non_null(n,"string_class",n.get_string_class())
  };

  override def visit_class_decl(the_node:Cclass_decl,name:Symbol,parent:Symbol,features:Features,filename:Symbol) : Any = {
    if (parent == native_sym) null
    else check_non_null(the_node,"superclass",the_node.get_superclass());
    super.visit_class_decl(the_node,name,parent,features,filename)
  };

  override def visit_method(the_node:Cmethod,overridep:Boolean,name:Symbol,formals:Formals,return_type:Symbol,expr:Expression) : Any = {
    check_non_null(the_node,"owner",the_node.get_owner());
    if (return_type == null_sym) null
    else if (return_type == nothing_sym) null
    else check_non_null(the_node,"(method)feature_of_class",
			the_node.get_feature_of_class());
    super.visit_method(the_node,overridep,name,formals,return_type,expr)
  };

  override def visit_attr(the_node:Cattr,name:Symbol,of_type:Symbol) : Any = {
    check_non_null(the_node,"owner",the_node.get_owner());
    if (of_type == null_sym) null
    else if (of_type == nothing_sym) null
    else check_non_null(the_node,"(attr)feature_of_class",
			the_node.get_feature_of_class());
    super.visit_attr(the_node,name,of_type)
  };

  override def visit_formal(the_node:Cformal,name:Symbol,of_type:Symbol) : Any = {
    if (of_type == null_sym) null
    else if (of_type == nothing_sym) null
    else check_non_null(the_node,"formal_of_class",
			the_node.get_formal_of_class());    
    super.visit_formal(the_node,name,of_type)
  };

  override def visit_branch(the_node:Cbranch,name:Symbol,local_type:Symbol,expr:Expression) : Any = {
    check_non_null(the_node,"case_of_type",the_node.get_case_of_type());
    if (local_type == null_sym) null
    else check_non_null(the_node,"case_of_class",
			the_node.get_case_of_class());    
    super.visit_branch(the_node,name,local_type,expr)
  };

  override def visit_Expression(the_node:Expression) : Any = {
    check_non_null(the_node,"of_type",the_node.get_of_type());
    super.visit_Expression(the_node)
  };

  override def visit_let(the_node:Clet,identifier:Symbol,local_type:Symbol,init:Expression,body:Expression) : Any = {
    if (local_type == null_sym) null
    else if (local_type == nothing_sym) null
    else check_non_null(the_node,"of_class",the_node.get_of_class());
    super.visit_let(the_node,identifier,local_type,init,body)
  };

  override def visit_alloc(the_node:Calloc,type_name:Symbol) : Any = {
    check_non_null(the_node,"of_class",the_node.get_of_class());
    super.visit_alloc(the_node,type_name)
  };

  override def visit_assign(the_node:Cassign,name:Symbol,expr:Expression) : Any = {
    check_non_null(the_node,"binding",the_node.get_binding());
    super.visit_assign(the_node,name,expr)
  };

  override def visit_variable(the_node:Cvariable,name:Symbol) : Any = {
    check_non_null(the_node,"binding",the_node.get_binding());
    super.visit_variable(the_node,name)
  };

  override def visit_static_dispatch(the_node:Cstatic_dispatch,expr:Expression,type_name:Symbol,name:Symbol,actuals:Expressions) : Any = {
    check_non_null(the_node,"mbinding",the_node.get_mbinding());
    super.visit_static_dispatch(the_node,expr,type_name,name,actuals)
  };

  override def visit_dispatch(the_node:Cdispatch,expr:Expression,name:Symbol,actuals:Expressions) : Any = {
    check_non_null(the_node,"mbinding",the_node.get_mbinding());
    super.visit_dispatch(the_node,expr,name,actuals)
  };

  def check_non_null(n : CoolNode, aname : String, binding : Any) : Any =
    if (is_null(binding))
      out("Attribute ").out_any(n).out(".").out(aname).out(" undefined.\n")
    else null;
}
class StripAttributes(var pa4 : Boolean) extends CoolTreeVisitor()
{
  var native_sym : Symbol = symbol("native");
  var null_sym : Symbol = symbol("null");

  override def visit_Program(n:Program) : Any = {
    if (pa4) {
      n.set_any_class(null);
      n.set_unit_class(null);
      n.set_int_class(null);
      n.set_boolean_class(null);
      n.set_string_class(null)
    } else ()
  };

  override def visit_Class(n : Class) : Any = {
    if (!pa4) {
      n.set_superclass(null)
    } else ()
  };

  override def visit_Feature(n:Feature) : Any = {
    if (pa4) {
      n.set_feature_of_class(null)
    } else {
      n.set_owner(null);
      n.set_overrides(null)
    }
  };

  override def visit_Formal(n : Formal) : Any =
  {
    if (pa4) {
      n.set_formal_of_class(null)
    } else ()
  };

  override def visit_Case(n : Case) : Any = {
    if (pa4) {
      n.set_case_of_class(null);
      n.set_case_of_type(null)
    } else ()
  };

  override def visit_Expression(n:Expression) : Any = {
    n.get_binding() match {
      case null =>
      case x:Cattr =>
	if (pa4) () else n.set_binding(null)
      case x:Any =>
	if (pa4) n.set_binding(null) else ()
    };
    if (pa4) {
      n.set_of_type(null); 
      n.set_of_class(null) 
    } else n.set_mbinding(null)
  };

}
/** Simple hash table with put/get/size/elements emethods.
 */
class Hashtable() extends IO()
{
  // #(
  var buckets : ArrayAny = new ArrayAny(10);
  var entries : Int = 0;

  def size() : Int = entries;

  def hash(key : Symbol) : Int = {
    var h : Int = key.hashCode();
    var m : Int = buckets.length();
    var p : Int = h/m * m;
    if (h < 0) p - h else h - p
  };

  def get(key : Symbol) : Any = {
    var i : Int = hash(key);
    var b : Hashbucket = null;
    buckets.get(i) match {
      case null => null
      case bb:Hashbucket => b = bb
    };
    var result : Any = null;
    while (!is_null(b)) {
      if (b.get_symbol() == key) {
	result = b.get_value();
	b = null
      } else b = b.get_next()
    };
    result
  };

  def put(key : Symbol, value : Any) : Any = {
    var i : Int = hash(key);
    var b : Hashbucket = null;
    var p : Any = null;
    buckets.get(i) match {
      case null => {
	buckets.set(i,new Hashbucket(key,value)); 
	entries = entries + 1
      }
      case bb:Hashbucket => b = bb
    };
    while (!is_null(b)) {
      if (b.get_symbol() == key) {
	p = b.get_value();
	b.set_value(value);
	b = null
      } else if (is_null(b.get_next())) {
	b.set_next(new Hashbucket(key,value));
	entries = entries + 1;
	if (buckets.length() < entries) rehash() else null;
	b = null
      } else {
	b = b.get_next()
      }
    };
    p
  };

  def elements() : Enumeration = new HashtableEnumeration(buckets);

  def rehash() : Unit = {
    var enum : Enumeration = elements();
    buckets = new ArrayAny(buckets.length()*2);
    entries = 0;
    while (enum.hasNext()) {
      enum.next() match {
	case p:Pair => 
	  p.first() match {
	    case s:Symbol => put(s,p.second())
	  }
      }
    }
  };
}

class Hashbucket(var symbol : Symbol, var value : Any) {
  var next : Hashbucket = null;

  def get_symbol() : Symbol = symbol;
  def get_value() : Any = value;
  def get_next() : Hashbucket = next;

  def set_value(v : Any) : Unit = value = v;
  def set_next(n : Hashbucket) : Unit = next = n;
}

class HashtableEnumeration(var buckets : ArrayAny) extends Enumeration() {
  var i : Int = -1;
  var b : Hashbucket = null;
  var io : IO = new IO();

  { move() };

  override def hasNext() : Boolean = i < buckets.length();

  override def next() : Any = {
    var result : Pair = new Pair(b.get_symbol(),b.get_value());
    b = b.get_next();
    move();
    result
  };

  def move() : Unit = {
    while (if (io.is_null(b)) {i=i+1;i} < buckets.length() else false) {
      buckets.get(i) match {
	case null => null
	case x:Hashbucket => b = x
      }
    }
  };
  // #)
  // PA1: TODO: Implement this class.
}
class Enumeration() extends IO() {
  def next() : Any = abort("no more elements");
  def hasNext() : Boolean = false;
}
class Pair(var v1 : Any, var v2 : Any) {
  def first() : Any = v1;
  def second() : Any = v2;
}
class A2I() {
  
  // Convert a string of digits into an integer.
  // return a negative number if something went wrong.
  def a2i(s : String) : Int = {
    var i : Int = 0;
    var result : Int = 0;
    while (if (result < 0) false else i < s.length()) {
      var digit : Int = c2i(s.substring(i,i+1));
      if (digit < 0) result = digit else result = result * 10 + digit;
      i = i + 1
    };
    result
  };

  //   c2i   Converts a 1-character string to an integer.  returns -1
  //         if the string is not "0" through "9"
  def c2i(char : String) : Int = {
    var ch : Int = char.charAt(0);
    if (ch < 48) -1
    else if (58 <= ch) -1
    else ch - 48
  };

  def i2a(i : Int) : String = i.toString();
}
/**
 * A simple class for building up strings.
 */
class StringBuilder() {
  var result : String = "";

  def append(s : String) : StringBuilder = {
    result = result.concat(s);
    this
  };

  def setLength(n : Int) : Unit = result = result.substring(0,n);

  override def toString() : String = result;
}
// A Main class to run the semantic analysis phase of the compiler
// as a standalone Cool program
class Main() extends Statistics() {
    var options : CoolOptions = new CoolOptions();
    var ctp : CoolTreeParser = new CoolTreeParser();

    {
      options.set_parse(false);
      ctp.start();
      var p : Program = ctp.parse_Program(0);
      ctp.resolve_attributes();
      if (!new Semant(p,options).run()) {
	out("Semant errors found\n")
      } else {
	p.accept(new CheckSemant());
	new CoolTreeDumper().dump(p)
      };
      if ("--show-statistics".equals(in())) {
	print()
      } else ()
    };
}
