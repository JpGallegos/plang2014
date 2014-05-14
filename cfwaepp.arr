#lang pyret/check

# cfwaepp.arr - Interpreter for CFWAE++
# Copyright (C) 2014 - Humberto Ortiz-Zuazaga <humberto.ortiz@upr.edu>
#                      John P. (Jp) Gallegos <sylladie@gmail.com>

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

# Data type for expressions
data FieldP:
  | fieldP (name :: String, value :: ExprP)
end

data ExprP:
  | ObjectP (fields :: List<FieldP>)

  | FuncP (args :: List<String>, body :: ExprP)
  | AppP (func :: ExprP, args :: List<ExprP>)
  | DefvarP (id :: String, bind :: ExprP, body :: ExprP)
  | DeffunP (name :: String, ids :: List<String>, funbody :: ExprP, body :: ExprP)
  | IdP (name :: String)

  | GetfieldP (o :: ExprP, field :: ExprP)
  | SetfieldP (o :: ExprP, field :: ExprP, newval :: ExprP)
  | SetvarP (id :: String, val :: ExprP)

  | WhileP (test :: ExprP, body :: ExprP)
  | ForP (init :: ExprP, test :: ExprP, update :: ExprP, body :: ExprP)

  | SeqP (es :: List<ExprP>)
  | IfP (cond :: ExprP, thn :: ExprP, els :: ExprP)

  | NumP (n :: Number)
  | StrP (s :: String)
  | TrueP
  | FalseP

# An op is one of '+ '- '== 'print '< '>
  | PrimP (op :: String, args :: List<ExprP>)
end                          

data FieldC:
  | fieldC (name :: String, value :: ExprC)
end

data ExprC:

  | ObjectC (fields :: List<FieldC>)
  | GetFieldC (obj :: ExprC, field :: ExprC)
  | SetFieldC (obj :: ExprC, field :: ExprC, value :: ExprC)

  | FuncC (args :: List<String>, body :: ExprC)
  | AppC (func :: ExprC, args :: List<ExprC>)
  | LetC (id :: String, bind :: ExprC, body :: ExprC)
  | IdC (id :: String)
  | SetC (id :: String, value :: ExprC)

  | IfC (cond :: ExprC, thn :: ExprC, els :: ExprC)
  | SeqC (e1 :: ExprC, e2 :: ExprC)

  | NumC (n :: Number)
  | StrC (s :: String)
  | TrueC
  | FalseC

  | ErrorC (expr :: ExprC)

# The core operations are 'String+ 'num+ 'num- '== '< '> 'print 'tagof
  | Prim1C (op :: String, arg :: ExprC)
  | Prim2C (op :: String, arg1 :: ExprC, arg2 :: ExprC)
end

# Environments and Values
data Binding:
  | bind (name :: String, value :: Number)
end

# Environments are lists of bindings
mt-env = []
xtnd-env = link

data FieldV:
  | fieldV (name :: String, value :: ValueC)
end

data ValueC:
  | TrueV
  | FalseV
  | NumV (n :: Number)
  | StrV (s :: String)
  | ClosureV (args :: List<String>, body :: ExprC, env :: List<Binding>)
  | ObjectV (fields :: List<FieldV>)
end

# Code: Humberto Ortiz
fun pretty-value(v :: ValueC) -> String:
  cases (ValueC) v:
    | ObjectV(_) => "object"
    | ClosureV(_, _, _) => "function"
    | NumV(n) => torepr(n)
    | StrV(s) => s
    | TrueV => "true"
    | FalseV => "false"
  end
end

# helper function for errors
interp-error = raise

# The store maps locations to values
data Cell:
  | cell (location :: Number, value :: ValueC)
end

# The store is a list of cells
mt-sto = []
xtnd-sto = link

data Result:
  | ret (value :: ValueC, store :: List<Cell>)
end

binops = ["+", "-", "==", "<", ">"]
unops = ["print", "tagof"]
keywords = ['if', 'fun', 'true', 'false', 'defvar', 'deffun', 'obj', 'getfield', 'setfield', 'setvar', 'begin', 'while', 'print', 'for']

# Code: Humberto Ortiz
fun parse-formals(s, illegals) -> List<String>:
  doc: "Read a list of identifiers S and construct a list of Strings."
  if List(s):
    cases (List) s:
      | empty => empty
      | link(first, rest) =>
        if illegals.member(first):
          raise("parse-formals: formal arguments must be named uniquely")
        else:
          link(first, parse-formals(rest, link(first, illegals)))
        end
    end
  else:
    raise("parse-formals: illegal formal arguments")
  end
where:
  parse-formals(["x", "y"], keywords) is ["x", "y"]
end

# Code: Humberto Ortiz
fun parse-fields(lof) -> List<FieldP>:
  doc: "Code by Humerto Ortiz."
  for map(field from lof):
    name = field.first
    val = parse(list.index(field, 1))
    fieldP(name, val)
  end
end

# Code: Humberto Ortiz
fun parse(s) -> ExprP:
  doc: "Parse reads an s-expression S and returns the abstract syntax tree."
  if Number(s):
    # num
    NumP(s)
  else if String(s):
    # true
    if s == "true":
      TrueP
    # false
    else if s == "false":
      FalseP
    # id
    else:
      IdP(s)
    end
  else if List(s):
    cases (List) s:
      | empty => raise("parse: empty sexpr")
      | link(op, r) =>
        len = r.length()
        # while
        if "while" == op:
          if len == 2:
            t = parse(list.index(r, 0))
            b = parse(list.index(r, 1))
            WhileP(t, b)
          else:
            raise("parse: malformed while" + s)
          end
        # string
        else if "string" == op:
          if len == 1:
            StrP(r.first)
          else:
            raise("parse: malformed string" + r)
          end
        # + - == < >
        else if binops.member(op):
          if len == 2:
            PrimP(op, [parse(list.index(r, 0)), parse(list.index(r, 1))])
          else:
            raise("parse: binary operations require two arguments")
          end
        # print
        else if "print" == op:
          if len == 1:
            PrimP(op, [parse(r.first)])
          else:
            raise("parse: print requires a single argument")
          end
        # if
        else if "if" == op:
          if len == 3:
            cond = parse(list.index(r, 0))
            then = parse(list.index(r, 1))
            esle = parse(list.index(r, 2))
            IfP(cond, then, esle)
          else:
            raise("parse: malformed if expression")
          end
        # begin
        else if "begin" == op:
          es = for map(e from r):
            parse(e)
          end
          SeqP(es)
        # defvar
        else if "defvar" == op:
          if len == 3:
            id = list.index(r, 0)
            val = parse(list.index(r, 1))
            bod = parse(list.index(r, 2))
            DefvarP(id, val, bod)
          else:
            raise("parse: malformed defvar")
          end
        # setvar
        else if "setvar" == op:
          if len == 2:
            id = list.index(r, 0)
            val = parse(list.index(r, 1))
            SetvarP(id, val)
          else:
            raise("parse: malformed setvar")
          end
        # for
        else if "for" == op:
          if len == 4:
            args = for map(arg from r):
              parse(arg)
            end
            init = list.index(args, 0)
            test = list.index(args, 1)
            update = list.index(args,2)
            body = list.index(args, 3)
            ForP(init, test, update, body)
          else:
            raise("parse: malformed for " + torepr(s))
          end
          # fun
        else if "fun" == op:
          if len == 2:
            formals = parse-formals(list.index(r, 0), keywords)
            body = parse(list.index(r, 1))
            FuncP(formals, body)
          else:
            raise("parse: malformed function definition")
          end
          # obj
        else if "obj" == op:
          if len == 1:
            ObjectP(parse-fields(r.first))
          else:
            raise("parse: malformed object" + torepr(s))
          end
          # getfield
        else if "getfield" == op:
          if len == 2:
            obj = parse(list.index(r, 0))
            field = parse(list.index(r, 1))
            GetfieldP(obj, field)
          else:
            raise("parse: malformed getfield" + torepr(s))
          end
          # setfield
        else if "setfield" == op:
          if len == 3:
            obj = parse(list.index(r, 0))
            field = parse(list.index(r, 1))
            val = parse(list.index(r, 2))
            SetfieldP(obj, field, val)
          else:
            raise("parse: malformed setfield" + torepr(s))
          end
          # deffun
        else if "deffun" == op:
          if len == 3:
            ids = list.index(r, 0)
            funbody = parse(list.index(r, 1))
            body = parse(list.index(r, 2))
            DeffunP(ids.first, ids.rest, funbody, body)
          else:
            raise("parse: malformed fun " + torepr(s))
          end
        else:
          # app
          AppP(parse(s.first), map(parse, s.rest))
        end
    end
  else:
    raise("parse: unknown expression " + torepr(s))
  end
where:
#  fun p(s): parse(read-sexpr(s)) end 
#  p("3") is NumP(3)
#  p("(while true 5)") is WhileP(TrueP, NumP(5))
#  p("(for (setvar x 0) (< x 10) (setvar x (+ x 1)) 
#    (print x))") is ForP(SetvarP("x", NumP(0)), PrimP("<", [IdP("x"), NumP(10)]), SetvarP("x", PrimP("+", [IdP("x"), NumP(1)])), PrimP("print", [IdP("x")]))
  # NOTE: strings must be enclosed in double quotes
  # You can put them inside single quotes, or escape them
#  p("\"hello\"") is StrP("hello")
#  p('"hello"') is StrP("hello")
#  p("(print (+ 2 3))") is PrimP("print", [PrimP("+", [NumP(2), NumP(3)])])
#  p("(if true 1 2)") is IfP(TrueP, NumP(1), NumP(2))
#  p("(begin 1 2 3)") is SeqP([NumP(1), NumP(2), NumP(3)])
#  p("(defvar x 1 x)") is DefvarP('x', NumP(1), IdP('x'))
#  p("(setvar x 2)") is SetvarP('x', NumP(2))
#  p("(for 0 true 1 2)") is ForP(NumP(0), TrueP, NumP(1), NumP(2))
#  p("(fun (x) x)") is FuncP(['x'], IdP("x"))
#  p("(obj ((x 1) (f (fun (x) x))))") is ObjectP([fieldP("x", NumP(1)), fieldP("f", FuncP(['x'], IdP("x")))])
#  p('(getfield o "x")') is GetfieldP(IdP('o'), StrP('x'))
#  p('(setfield o "x" 2)') is SetfieldP(IdP('o'), StrP('x'), NumP(2))
#  p("(deffun (id x) x 3)") is DeffunP("id", ["x"], IdP('x'), NumP(3)) 
#  p("(deffun (id x) x (id 3))") is DeffunP("id", ["x"], IdP('x'), AppP(IdP("id"), [NumP(3)])) 
end

# Code: Jp Gallegos
fun desugar(e :: ExprP) -> ExprC:
  doc: "Desugar the expression E, return the equivalent in the core language."
  cases (ExprP) e:
    | ObjectP(fields) => 
      desugared-fields = for map(f from fields):
        fieldC(f.name, desugar(f.value))
      end
      ObjectC(desugared-fields)

    | FuncP(args, body) => FuncC(args, desugar(body))
    | AppP(func, args-actual) => AppC(desugar(func), map(desugar, args-actual))
    | DefVarP(id, bnd, body) => LetC(id, desugar(bnd), desugar(body))
    | DeffunP(name, ids, funcbody, body) => 
      dummy-fun = FuncC([], ErrorC(StrC("dummy function")))
      LetC(name, dummy-fun,
           SeqC(SetC(name, 
                     FuncC(ids, desugar(funcbody)), 
                     desugar(body))))  # Chapter 17: Recursion
    | IdP(name) => IdC(name)

    | GetfieldP(obj, field) => GetFieldC(desugar(obj), desugar(field))
    | SetfieldP(obj, field, newval) => SetFieldC(desugar(obj), desugar(field), desugar(newval))
    | SetvarP(id, val) => SetC(id, desugar(val))

    # Code: Humberto Ortiz
    | WhileP(test, body) =>
      dummy-fun = FuncC([], ErrorC(StrC("Dummy function")))
      IfC( desugar(test),
       # while-var will hold the actual function once we tie
       # everything together
       LetC( "while-var", dummy-fun,
         LetC( "while-func", 
           # this function does the real work - it runs the body of
           # the while loop, then re-runs it if the test is true, and
           # stops if its false
            FuncC([],
              LetC("temp-var",
                desugar( body),
               IfC(desugar( test),
                  AppC(IdC( "while-var"), []),
                  IdC( "temp-var")))),
           # The SetC here makes sure that 'while-var will resolve
           # to the right value later, and the AppC kicks things off
           SeqC(SetC( "while-var", IdC( "while-func")),
              AppC(IdC("while-var"), [])))),
       FalseC)
    # End code by Humberto Ortiz
    | ForP(init, test, update, body) => 
      # Python:
      # with desugar(init) as init_var:
          # if desugar(test):
              # with lambda: raises("Dummy fun") as for_var:
                  # def for_func():
                  #   
          # else:
              # return init-var
      can-do = desugar(test)
      dummy-fun = FuncC([], ErrorC(StrC("Dummy function")))
      LetC("init-var", desugar(init),      
            IfC(can-do,                    
                LetC("for-var", dummy-fun, 
                     LetC("for-func", 
                          FuncC([], 
                                LetC("temp-body", desugar(body), 
                                     LetC("temp-update", desugar(update), 
                                          IfC(can-do, 
                                              AppC(IdC("for-var"), []), 
                                              IdC("temp-body"))))), 
                          SeqC(SetC("for-var", IdC("for-fun"), 
                               AppC(IdC("for-var"), []))))),
                IdC("init-var")))          # 3 b) If v2 is false yield v as the result for the whole expression
    
    | SeqP(es) => create-seq(es)
    | IfP(cond, thn, els) => IfC(desugar(cond), desugar(thn), desugar(els))

    | NumP(n) => NumC(n)
    | StrP(s) => StrC(s)
    | TrueP => TrueC
    | FalseP => FalseC

    # An op is one of "'+', '-', '==', 'print', '<', '>'"
    # Note to self: No way in hell I'm writing a test for this.
    # If INTERP gets a bad case of the explosive shits with PRIM2C: CHECK HERE FIRST.
    # In God we trust.
    | PrimP(op, args) => 
      if op == "print":
        if args.length() == 1:
          Prim1C(op, desugar(args.first))
        else:
          ErrorC(StrC(""))
        end
      else:
        arg1 = desugar(list.index(args, 0))
        arg2 = desugar(list.index(args, 1))
        IfC(Prim2C("==", Prim1C("tagof", arg1), Prim1C("tagof", arg2)),                                # if tagof(ar1) == tagof(arg2):
                                                                                                           #(Note: If tagof(arg1) == tagof(arg2) and tagof(arg1) == Some-type-value
                                                                                                           # then tagof(arg2) == some-type-value)
            IfC(Prim2C("==", Prim1C("tagof", arg1), StrC("string")),                                     # if tagof(arg1) == "string":
                IfC(Prim2C("==", StrC(op), StrC("+")),                                                     #if op == "+":
                    Prim2C("num+", arg1, arg2),                                                              # Prim2C("string+", desugar(arg1), desugar(arg2))
                    IfC(Prim2C("==", StrC(op), StrC("==")),                                                # else if op == "==":
                        Prim2C(op, arg1, arg2),                                                              # Prim2C("==", desugar(arg1), desugar(arg2))
                        ErrorC(StrC("Bad args to prim: incorrect argument type(s) for operator")))),       # else: ErrorC("Wrong types of operand for operator")
                IfC(Prim2C("==", Prim1C("tagof", arg1), StrC("number")),                                 # else if tagof(arg1) == "number":
                    IfC(Prim2C("==", StrC(op), StrC("+")),                                                 # if op == "+": 
                        Prim2C("num+", arg1, arg2),                                                          # Prim2C("num+", desugar(arg1), desugar(arg2))
              # Ok, so I'm cheating a little: since "-" only works on number values I am ignoring "num-"
              # and passing "-" directly to avoid more damned IfC's...
                        Prim2C(op, arg1, arg2)),                                                           # else: Prim2C(op, desugar(arg1), desugar(arg2)) 
                    IfC(Prim2C("==", StrC(op), StrC("==")),                                              # else if tagof(arg1) is some other value type:
                        Prim2C(op, arg1, arg2),                                                            # Prim2C("==", desugar(arg1), desugar(arg2))                                                
                        ErrorC(StrC("Bad args to prim: incorrect argument type(s) for operator"))))),    # else: ErrorC("Wrong operands for operator")
            ErrorC(StrC("Bad args to prim: types don't match each other")))                            # else: ErrorC("Argument types don't match")
      end
  end
where:
#  fun run(s): desugar(parse(read-sexpr(s))) end
#  run("0") is NumC(0)
#  run("(while true 1)") is IfC(TrueC, LetC("while-var", FuncC([], ErrorC(StrC("Dummy function"))), LetC("while-func", FuncC([], LetC("temp-var", NumC(1), IfC(TrueC, AppC(IdC("while-var"), []), IdC("temp-var")))), SeqC(SetC("while-var", IdC("while-func")), AppC(IdC("while-var"), [])))), FalseC)
end


# Templates for interpreter: fix interp-full
# Code: Jp Gallegos, Humberto Ortiz
fun interp-full (expr :: ExprC, env :: List<Binding>, store :: List<Cell>) -> Result:
  op-table = [["num+", plus-num], ["num-", sub-num], ["string+", plus-str], ["<", less-than], [">", greater-than], ["==", equal], ["print", print-value], ["tagof", tag]]
  cases (ExprC) expr:
    # Primitives
    | NumC (n) => ret(NumV(n), store)
    | TrueC => ret(TrueV, store)
    | FalseC => ret(FalseV, store)
    | StrC(s) => ret(StrV(s), store)

    # Objects
    | ObjectC(fields) => raise("Not implemented")
    | GetFieldC(obj, field) => raise("Not implemented")
    | SetFieldC(obj, field, value) => raise("Not implemented")

    # Functions
    | FuncC(args, body) => ret(ClosureV(args, body, env), store)
    | AppC(func, args) => raise("Not implemented")
    | LetC(id, bnd, body) => raise("Not implemented")
    | IdC(id) => ret(fetch(lookup(id, env), store), store)
    | SetC(e1, e2) => raise("Not implemented")
    
    # Error
    | ErrorC(e) =>   
        error-msg = interp-full(e, env, store)   
        if is-StrV(error-msg.value):
          interp-error(error-msg.value.s)
        else:
          interp-error(pretty-value(error-msg.value))
        end

    # Control Structures
    | IfC(cond, thn, els) => raise("Not implemented")
    | SeqC(e1, e2) =>
        e1-value = interp-full(e1, env, store)
        interp-full(e2, env, e1-value.st)

    # Core operations
    | Prim1C(op, arg) => 
        arg-v = interp-full(arg, env, store)
        ret(apply-unop-fun(op, op-table, arg-v.value), arg-v.store)
    | Prim2C(op, arg1, arg2) => 
        arg1-v = interp-full(arg1, env, store)
        arg2-v = interp-full(arg2, env, arg1-v.store)
        ret(apply-binop-fun(op, op-table, arg1-v.value, arg2-v.value), arg2-v.store)
  end
end

# Code: Humberto Ortiz
fun interp(expr :: ExprC) -> ValueC:
  cases (Result) interp-full(expr, mt-env, mt-sto):
    | ret (value, store) => value
  end
end

check:
  interp(NumC(5)) is NumV(5)
  interp(TrueC) is TrueV
  interp(FalseC) is FalseV
  interp(StrC("Hi!")) is StrV("Hi!")
  interp(ErrorC(StrC("Oops"))) raises "Oops"
  interp(ErrorC(TrueC)) raises "true"
end

# Auxiliary functions
# Code: Jp Gallegos
fun fetch(n :: Number, st :: List<Cell>) -> ValueC:
  cases (List<Cell>) st:
    | empty => raise("Store: unbound location")
    | link(entry, rest) =>
        if n == entry.location:
          entry.value
        else:
          fetch(n , rest)
        end
  end
end

fun lookup(s :: String, nv :: List<Binding>) -> Number:
  cases (List<Binding>) nv:
    | empty => raise("Environment: unbound identifier")
    | link(entry, rest) =>
        if s == entry.name:
          entry.value
        else:
          lookup(s, rest)
        end
  end
end

fun lookup-field(o :: ValueC, f :: ValueC) -> ValueC:
  doc: "Lookup(vo, vf) metafunction from the ParselTongue specification. Searches for field f in ObjectV o.
  Yields the value of field f if found, raises and exception otherwise."

  if not is-ObjectV(o):
    raise("Non-object in field update: " + pretty-value(o))
  else if not is-StrV(f):
    raise("Non-string in field update: " + pretty-value(f))
  else:
    lookup-field-aux(o.fields, f.s)
  end
end

fun lookup-field-aux(fields :: List<FieldV>, f :: String) -> ValueC:
  cases (List<FieldV>) fields:
    | empty => raise("Field not found: " + f)
    | link(entry, rest) =>
        if entry.name == f:
          entry.value
        else:
          lookup-field-aux(rest, f)
        end
  end
end

fun update-object(o :: ValueC, f :: ValueC, new-val :: ValueC) -> ValueC:
  doc: "UpdateObject(vo, vf, vnew) metafunction from the ParselTongue specification. Searches for field f in ObjectV o.
  If found, yields a new ObjectV with the replaced field f with value new-val; otherwise it yields a new 
  ObjectV with all the fields of o, plus a new field f mapped to new-val."
  
  if not is-ObjectV(o):
    raise("Non-object in field update: " + pretty-value(o))
  else if not is-StrV(f):
    raise("Non-string in field update: " + pretty-value(f))
  else:
    var found = false
    new-fields = for map(field from o.fields):
      if field.name == f.s:
        found := true
        fieldV(field.name, new-val)
      else:
        field
      end
    end

    if found:
      ObjectV(new-fields)
    else:
      ObjectV(link(fieldV(f.s, new-val), new-fields))
    end
  end
end

fun add-binding(env :: List<Binding>, id :: String, location :: Number) -> List<Binding>:
  doc: "AddBinding(env, identifier, location) metafunction from the ParselTongue specification. Search the
  environment env for id. If found, replace the mapping with one from id to location; otherwise,
  add a binding to env from id to location. Yield the resulting env."
  
  var found = false

  new-env = for map(entry from env):
    if entry.name == id:
      found := true
      bind(id, location)
    else:
      entry
    end
  end

  if found:
    new-env
  else:
    link(bind(id, location), new-env)
  end
where:
  env = [bind("s", 0), bind("stuff", 1)]
  add-binding(env, "foo", 3) is [bind("foo", 3), bind("s", 0), bind("stuff", 1)]
  add-binding(env, "stuff", 5) is [bind("s", 0), bind("stuff", 5)]
end

fun update-store(store :: List<Cell>, location :: Number, value :: ValueC) -> List<Cell>:
  doc: "UpdateStore(store, location, value) metafunction from the ParselTongue specification.
  Search store for location. If found, replace mapping with one from location to value; otherwise,
  add a mapping to store from location to value. Yield the resulting store."

  var found = false
  
  new-store = for map(entry from store):
    if entry.location == location:
      found := true
      cell(location, value)
    else:
      entry
    end
  end

  if found:
    new-store
  else:
    link(cell(location, value), new-store)
  end
where:
  store = [cell(0, NumV(5)), cell(1, StrV("stuff"))]
  update-store(store, 3, StrV("Bar")) is [cell(3, StrV("Bar")), cell(0, NumV(5)), cell(1, StrV("stuff"))]
  update-store(store, 1, NumV(6)) is [cell(0, NumV(5)), cell(1, NumV(6))]
end

fun create-seq(es :: List<ExprP>) -> ExprC:
  cases (List<ExprP>) es:
    | empty => ErrorC(StrC("create-seq: malformed SeqP"))
    | link(expr, rest) =>
      if rest == empty:
        desugar(expr)
      else: 
        SeqC(desugar(expr), desugar(rest.first))
      end
  end
where:
  create-seq([TrueP]) is TrueC
  create-seq([TrueP, FalseP]) is SeqC(TrueC, FalseC)
end

fun op-table-search(op :: String, table :: List):
  cases (List) table:
    | empty => raise("Operator not defined")
    | link(entry, rest) =>
        if list.index(entry, 0) == op:
          list.index(entry, 1)
        else:
          op-table-search(op, rest)
        end
  end
end

fun apply-binop-fun(op :: String, op-table :: List, l :: ValueC, r :: ValueC) -> ValueC:
  bin-op = op-table-search(op, op-table)
  bin-op(l, r)
end

fun apply-unop-fun(op :: String, op-table :: List, v :: ValueC) -> ValueC:
  un-op = op-table-search(op, op-table)
  un-op(v)
end

# Operators:
# - num+
fun plus-num(v1 :: ValueC, v2 :: ValueC) -> ValueC: 
  if (not is-NumV(v1)) or (not is-NumV(v2)):
    raise("Bad arguments for num+: " + pretty-value(v1) + " " + pretty-value(v2))
  else:
    NumV(v1.n + v2.n)
  end
end

# - num-
fun sub-num(v1 :: ValueC, v2 :: ValueC) -> ValueC: 
  if (not is-NumV(v1)) or (not is-NumV(v2)):
    raise("Bad arguments for num-: " + pretty-value(v1) + " " + pretty-value(v2))
  else:
    NumV(v1.n + v2.n) 
  end
end

# - string+
fun plus-str(v1 :: ValueC, v2 :: ValueC) -> ValueC: 
  if (not is-StrV(v1)) or (not is-StrV(v2)): 
    raise("Bad arguments for string+: " + pretty-value(v1) + " " + pretty-value(v2))
  else: 
    StrV(v1.s + v2.s) 
  end
end

# - == 
fun equal(v1 :: ValueC, v2 :: ValueC) -> ValueC:
  doc: "Equal(value1, value2) metafuntion from ParselTongue specification. 
      - Equal(string, string) => true for identical strings
      - Equal(number, number) => true for identical numbers
      - Equal(true, true) => true
      - Equal(false, false) => true
      - Equal({string1 : value1, ...}, {string2 : value2, ...}) => true when the same
      strings are in the same order, and when Equal(value1, value2) ... for all the 
      values, in order. (At each position, the fields are pairwise equal).
      - Equal(lambda1 (id1, ...) {expression1}, lambda2 (id2, ...) {expression2}) => true
      when the environment maps the same identifiers to Equal values, and when expression1
      is the same as expression2.
      - Equal(v1, v2) => false in all other cases."
  
  # Following the previously mentioned logic that: if tagof(v1) == tagof(v2), and 
  # tagof(v1) == type, then, necessarily, tagof() == type.
  if tag(v1) <> tag(v2):
    FalseV
  else:
    cases (ValueC) v1:
      | TrueV => 
          if v2 == TrueV:
            TrueV
          else:
            FalseV
          end
      | FalseV => 
          if v2 == FalseV:
            TrueV
          else:
            FalseV
          end
      | NumV(n) => 
          if n == v2.n:
            TrueV
          else:
            FalseV
          end
      | StrV(s) =>
          if s == v2.s:
            TrueV
          else:
            FalseV
          end
      | Closure(arg, body, env) => 
          if (arg.length() <> v2.arg.length()) or (env.length() <> v2.env.length()):
            FalseV
          else:
            if lambda-arg-equality(arg, v2.arg) and lambda-env-equality(env, v2.env) and exprc-equality(body, v2.body):
              TrueV
            else:
              FalseV
            end
          end
      | ObjectV(fields) => 
          if v1.fields.length() <> v2.fields.length():
            # if the fields of both values are not the same length
            # then the values are not the same, and we won't waste 
            # resources with more rigorous testing.
            FalseV
          else:
            object-equality(v1.fields, v2.fields)
          end
    end
  end
end

fun object-equality(v1-fields :: List<FieldV>, v2-fields :: List<FieldV>) -> ValueC:
  if (v1-fields == empty) and (v2-fields == empty):
    # We got here with one of two cases: case 1) both objects have no fields, both are equal;
    # case 2) after going through each of the fields in both Objects, we got to the end with 
    # all the conditions of equality being met, both are equal.
    # Either way, both are equal.
    TrueV
  else:
    v1-entry = v1-fields.first
    v2-entry = v2-fields.first
    
    if (v1-entry.name == v2-entry.name) and (equal(v1-entry.value, v2-entry.value) == TrueV):
      object-equality(v1-fields.rest, v2-fields.rest)
    else:
      FalseV
    end
  end
end

fun lambda-arg-equality(v1-args :: List<String>, v2-args :: List<String>) -> Bool:
  if (v1-args == empty) and (v2-args == empty):
    # See object-equality-eval for reasoning
    TrueV
  else:
    if (v1-args.first == v1-args.first):
      lambda-arg-equality(v1-args.rest, v2-args.rest)
    else:
      FalseV
    end
  end
end

fun lambda-env-equality(v1-env :: List<Binding>, v2-env :: List<Binding>) -> Bool:
  if (v1-env == empty) and (v2-env == empty):
    # By now you should probably get where I'm going with this.
    TrueV
  else:
    v1-entry = v1-env.first
    v2-entry = v2-env.first
    if (v1-entry.name == v2-entry.name) and (equal(v1-entry.value, v2-entry.value) == TrueV):
      lambda-env-equality(v1-env.rest, v2-env.rest)
    else:
      FalseV
    end
  end
end

fun exprc-lst-equality(v1 :: List<ExprC>, v2 :: List<ExprC>) -> Bool:
  if (v1 == empty) and (v2 == empty):
    true
  else:
    if exprc-equality(v1.first, v2.first):
      exprc-lst-equality(v1.rest, v2.rest)
    else:
      false
    end
  end
end

fun fieldc-equality(f1 :: List<FieldC>, f2 :: List<FieldC>) -> Bool:
  if (f1 == empty) and (f2 == empty):
    true
  else:
    if (f1.first.name == f2.first.name) and exprc-equality(f1.first.value, f2.first.value):
      fieldc-equality(f1.rest, f2.rest)
    else:
      false
    end
  end
end

fun exprc-equality(v1 :: ExprC, v2 :: ExprC) -> Bool:
  if exprc-tag(v1) <> exprc-tag(v2):
    false
  else:
    cases (ExprC) v1:
      | ObjectC(fields) => 
          if fields.length() <> v2.fields.length():
            false
          else:
            fieldc-equality(fields, v2.fields)
          end
      | GetFieldC(o, field) =>   
          exprc-equality(o, v2.o) and 
          exprc-equality(field, v2.field)
      | SetFieldC(o, field, value) => 
          exprc-equality(o, v2.o) and 
          exprc-equality(field, v2.field) and 
          exprc-equality(value, v2.value)
    
      | FuncC(args, body) =>
          if args.length() <> v2.args.length():
            false
          else:
            exprc-equality(args, v2.args) and 
            exprc-equality(body, v2.body)
          end
      | AppC(func, args) => 
          exprc-equality(func, v2.func) and
          exprc-lst-equality(args, v2.args)
          
      | LetC(id, bnd, body) => 
          (id == v2.id) and 
          exprc-equality(bnd, v2.bnd) and 
          exprc-equality(body, v2.body)
      | IdC(id) => id == v2.id
      | SetC(id, value) => 
          (id == v2.id) and 
          exprc-equality(value, v2.value)

      | IfC(cond, thn, els) => 
          exprc-equality(cond, v2.cond) and 
          exprc-equality(thn, v2.thn) and 
          exprc-equality(els, v2.els)
      | SeqC(e1, e2) => 
          exprc-equality(e1, v2.e1) and 
          exprc-equality(e2, v2.e2)
      
      | NumC(n) => n == v2.n
      | StrC(s) => s == v2.s
      | TrueC => is-TrueC(v2)
      | FalseC => is-FalseC(v2)

      | ErrorC(expr) => exprc-equality(expr, v2.expr)
      
      | Prim1C(op, arg) => 
          (op == v2.op) and 
          exprc-equality(arg, v2.arg)
      | Prim2C(op, arg1, arg2) => 
          (op == v2.op) and 
          exprc-equality(arg1, v2.arg1) and 
          exprc-equality(arg2, v2.arg2)
    end
  end
where:
  exprc-equality(ObjectC([]), ObjectC([])) is true
  exprc-equality(ObjectC(["foo", StrC("Bar")]), ObjectC(["foo", StrC("Bar")])) is true
end

fun exprc-tag(v :: ExprC) -> String:
  cases (ExprC) v:
    | ObjectC(_) => "Object"
    | GetFieldC(_, _) => "GetField"
    | SetFieldC(_, _, _) => "SetField"
    
    | FuncC(_, _) => "Func"
    | AppC(_, _) => "App"
    | LetC(_, _) => "Let"
    | IdC(_) => "IdC"
    | SetC(_, _) => "Set"

    | NumC(_) => "Num"
    | StrC(_) => "Str"
    | TrueC => "True"
    | FalseC => "False"

    | ErrorC(_) => "Error"
    
    | Prim1C(_, _) => "Prim1"
    | Prim2C(_, _, _) => "Prim2"
  end 
end 

# - >
fun greater-than(v1 :: ValueC, v2 :: ValueC) -> ValueC:
  if (not is-NumV(v1)) or (not is-NumV(v2)):
    raise("Bad arguments for >: " + pretty-value(v1) + " " + pretty-value(v2))
  else:
    if v1.n > v2.n:
      TrueV
    else:
      FalseV
    end
  end
where:
  greater-than(NumV(5), NumV(6)) is FalseV
  greater-than(NumV(6), NumV(5)) is TrueV
  greater-than(NumV(5), ObjectV([])) raises "Bad arguments for >: 5 object"
end

# - <
fun less-than(v1 :: ValueC, v2 :: ValueC) -> ValueC:
  if (not is-NumV(v1)) or (not is-NumV(v2)):
    raise("Bad arguments for <: " + pretty-value(v1) + " " + pretty-value(v2))
  else:
    if v1.n < v2.n:
      TrueV
    else:
      FalseV
    end
  end
where:
  less-than(NumV(5), NumV(6)) is TrueV
  less-than(NumV(6), NumV(5)) is FalseV
  less-than(NumV(5), ObjectV([])) raises "Bad arguments for <: 5 object"
end

# - tagof
fun tag(v :: ValueC) -> String:
  cases (ValueC) v:
    | ObjectV(_) => "object"
    | ClosureV(_, _, _) => "function"
    | NumV(_) => "number"
    | StrV(_) => "string"
    | TrueV => "boolean"
    | FalseV => "boolean"
   end
end

# - print
fun print-value(v :: ValueC) -> ValueC:
  print(pretty-value(v))
  # Since interp-full has to return something...
  v
end