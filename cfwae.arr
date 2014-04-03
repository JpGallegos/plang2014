#lang pyret/check
# cfwae.arr - Simple interpreter for CFWAE
# Copyright (C) 2014 - John P. Gallegos <sylladie@gmail.com>

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

# Bindings map identifiers to expressions
data Binding:
  | bind (name :: String, expr :: CFWAE)
end

# An Environment is a List<Env>
data Env:
  | env (name :: String, value :: CFWAE-Value)
end

mt-env = []
xtnd-env = link

# List of reserved keywords
keywords = ["+", "-", "*", "/", "with", "if0", "fun"]

# Data type for expressions
                          
data CFWAE:
  | numC (n :: Number)
  | binopC (op :: String, l :: CFWAE, r :: CFWAE)
  | withC (bindings :: List<Binding>, expr :: CFWAE)
  | idC (name :: String)
  | if0C (test-expr :: CFWAE, then-expr :: CFWAE, else-expr :: CFWAE)
  | fdC (args :: List<String>, body :: CFWAE)
  | appC (f :: CFWAE, args :: List<CFWAE>)
end

# and values
data CFWAE-Value:
  | numV (n :: Number)
  | closV (f :: CFWAE, e :: List<Env>) # ExprC must be an fdC
end
              
fun parse(s) -> CFWAE:
  doc: "Parse reads an s-expression S and returns the abstract syntax tree."
  if Number(s):
    numC(s)
  else if String(s):
    idC(s)
  else if List(s): 
    cases (List) s:
      | empty => raise("parse: unexpected empty list")
      | link(op, args) =>
        len-args = args.length()
        if (op == "+") or (op == "-") or (op == "*") or (op == "/"):
          if len-args == 2:
            argL = list.index(args, 0)
            argR = list.index(args, 1)
            binopC(op, parse(argL), parse(argR))
          else:
            raise("parse: incorrect amount of binopC args - " + len-args.tostring())
          end
        else if op == "with":
          if len-args == 2: 
            bind-lst = list.index(args, 0)
            body = list.index(args, 1)
            withC(create-bindings(bind-lst, []), parse(body))
          else:
            raise("parse: incorrect amount of withC args - " + len-args.tostring())
          end
        else if op == "if0":
          if len-args == 3:
            argIf = list.index(args, 0)
            argThen = list.index(args, 1)
            argElse = list.index(args, 2)
            if0C(parse(argIf), parse(argThen), parse(argElse))
          else:
            raise("parse: incorrect amount of if0C args - " + len-args.tostring())
          end
        else if op == "fun":
          if len-args == 2:
            if legal-id(list.index(args, 0), keywords):
              formal-args = list.index(args, 0)
              body = list.index(args, 1)  
              fdC(formal-args, parse(body))
            else:
              raise("parse: illegal parameter names")
            end
          else: 
            raise("parse: incorrect amout of fdC args - " + len-args.tostring())
          end
        else:
          appC(parse(op), map(parse, args))
        end
    end
  else:
    raise("parse: not number, list, or identifier")
  end
where:
  parse(read-sexpr("3")) is numC(3)

  fun p(s): parse(read-sexpr(s));
  p("()") raises "parse: unexpected empty list"
  p("(+ 2 1 3)") raises "parse: incorrect amount of binopC args - 3" 
  p("(+ 2)") raises "parse: incorrect amount of binopC args - 1" 
  p("(with ((x 3) (y 2)))") raises "parse: incorrect amount of withC args - 1"
  p("(with (x 3) (y 2) (+ x y))") raises "parse: incorrect amount of withC args - 3"
  p("(with ((x 2) (x 3)) (+ x 2))") raises "x is defined twice"
  p("(if0 2)") raises "parse: incorrect amount of if0C args - 1"
  p("(if0 (- 2 3) 4 5 (- 5 4))") raises "parse: incorrect amount of if0C args - 4"
  p("(fun (fun 2) (+ fun 2))") raises "parse: illegal parameter names"
  p("(fun (x x) (+ x x))") raises "parse: illegal parameter names"
  p("(fun (+ x y))") raises "parse: incorrect amout of fdC args - 1"
  p("(fun x y (+ x y))") raises "parse: incorrect amout of fdC args - 3"
  p("3") is numC(3)
  p("(+ 2 3)") is binopC("+", numC(2), numC(3))
  p("(if0 0 1 2)") is if0C(numC(0), numC(1), numC(2))
  p("(if0 1 2 3)") is if0C(numC(1), numC(2), numC(3))
  p("(with ((x 2) (y 3)) (+ x y))") is withC([bind("x", numC(2)), bind("y", numC(3))], binopC("+", idC("x"), idC("y")))
  p("(with ((x 2) (x 3)) (+ x y))") raises "x is defined twice"
  p("(fun () 5)") is fdC([], numC(5))
  p("(fun (x y) (+ x y))") is fdC(["x", "y"], binopC("+", idC("x"), idC("y")))
  p("((fun (x y) (* x y)) 2 3)") is appC(fdC(["x", "y"], binopC("*", idC("x"), idC("y"))), [numC(2), numC(3)])
  p("((fun (self n) (self self n)) (fun (self n) (if0 n 0 (+ n (self self (- n 1))))) 10)") is 
      appC(fdC(["self", "n"], appC(idC("self"), [idC("self"), idC("n")])), [fdC(["self", "n"], if0C(idC("n"), numC(0), binopC("+", idC("n"), appC(idC("self"), [idC("self"), binopC("-", idC("n"), numC(1))])))), numC(10)])
           
end

fun interp(e :: CFWAE) -> CFWAE-Value:
  doc: "Execute the expression E, return the result of evaluation."
  interp-helper(e, mt-env)
where:
  interp(if0C(numC(0), numC(1), numC(2))) is numV(1)
  interp(if0C(numC(1), numC(3), numC(2))) is numV(2)
end

check:
  fun run(s): interp(parse(read-sexpr(s))) end
  run("(if0 0 1 2)") is numV(1)
  run("(if0 1 2 3)") is numV(3)
  run("(with ((x 2) (y 3)) (with ((z (+ x y))) (+ x z)))") is numV(7)
  run("(with ((f (fun () 0))) (f))") is numV(0)
  run("((fun (self n) (self self n)) (fun (self n) (if0 n 0 (+ n (self self (- n 1))))) 10)") is numV(55)
  run("((fun (self n) (self self n)) (fun (self n) (if0 n 1 (* n (self self (- n 1))))) 5)") is numV(120)
  interp(binopC("%", numC(2), numC(3))) raises "Binary operator not defined"
  run("((2) 2 3)") raises "interp: incorrect f value for appC"
  run("((fun (x y) (+ x y)) 2)") raises "interp: arity mismatch"
end


# ---- Helper functions ----

fun interp-helper(e :: CFWAE, nv :: List<Env>) -> CFWAE-Value:
  doc: ""

  # -- Arithmetic helper functions --
  # Takes two numC values and returns a numV
  fun plus-v(v1, v2): numV(v1.n + v2.n);
  fun mult-v(v1, v2): numV(v1.n * v2.n);
  fun sub-v(v1, v2): numV(v1.n - v2.n);
  fun div-v(v1, v2): numV(v1.n / v2.n);

  fun binop-table-search(op :: String, table :: List):
    cases (List) table:
      | empty => raise("Binary operator not defined")
      | link(entry, rest) =>
        if list.index(entry, 0) == op:
          list.index(entry, 1)
        else:
          binop-table-search(op, rest)
        end
    end
  end

  fun apply-binop-fun(op :: String, l :: CFWAE-Value, r :: CFWAE-Value) -> CFWAE-Value:
    bin-op = binop-table-search(op, binop-table)
    bin-op(l, r)
  end

  binop-table = [["+", plus-v], ["-", sub-v], ["*", mult-v], ["/", div-v]]

  cases (CFWAE) e:
    | numC(n) => numV(n)
    | binopC(op, l, r) => 
      apply-binop-fun(op, interp-helper(l, nv), interp-helper(r, nv))
    | withC(bnd, body) =>
      new-env = for map(b from bnd):
        env(b.name, interp-helper(b.expr, nv))
      end
      interp-helper(body, new-env.append(nv))
    | idC(n) => lookup(n, nv)
    | if0C(tst, thn, els) =>
      if interp-helper(tst, nv) == numV(0):
        interp-helper(thn, nv)
      else:
        interp-helper(els, nv)
      end
    | fdC(_,_) => closV(e, nv)
    | appC(f, formal-args) =>
      clos = interp-helper(f, nv)
      if is-closV(clos):
        if clos.f.args.length() == formal-args.length():
          new-env = for map2(s from clos.f.args, a from formal-args):
            env(s, interp-helper(a, nv))
          end
          interp-helper(clos.f.body, new-env.append(clos.e))
        else:
          raise("interp: arity mismatch")
        end
      else:
        raise("interp: incorrect f value for appC")
      end
  end
end

# -- Miscellaneous --
fun create-bindings(lst :: List, bind-lst :: List<Binding>) -> List<Binding>:
  doc: "Takes lst, a list in the form of ((String value)...), and bind-lst, 
        and binds each String with a value."
  cases (List) lst:
    | empty => empty
    | link(front, rest) =>
      if is-link(front):
        name = front.first
        if legal-id(name, keywords):
          if not-defined(name, bind-lst):
            expr = parse(front.rest.first)
            current-bind = bind(name, expr)
            link(current-bind, create-bindings(rest, link(current-bind, bind-lst)))
          else:
            raise(name + " is defined twice")
          end
        else:
          raise(name + " is not a legal identifier name")
        end
      else:
       raise("Incorrect value for a list of bindings. Expected ((String Value)...)")
      end
  end
where: 
  create-bindings(read-sexpr("((x 2) (y 3))"), []) is [bind("x", numC(2)), bind("y", numC(3))]
  create-bindings(read-sexpr("((x 2) (x 3))"), []) raises "x is defined twice"
  create-bindings(read-sexpr("((fun 2))"), []) raises "fun is not a legal identifier name"
  create-bindings(read-sexpr("(2 3)"), []) raises "Incorrect value for a list of bindings. Expected ((String Value)...)"
end

fun not-defined(s :: String, nv :: List<Binding>) -> Bool:
  doc: "Searches a List<Binding> nv for String s. Returns
        true if s is not found, false otherwise."
  cases (List<Binding>) nv:
    | empty => true
    | link(front, rest) =>
      if s == front.name:
        false
      else:
        not-defined(s, rest)
      end
  end
where:
  not-defined("x", [bind("z", numC(2)), bind("y", numC(3)), bind("x", numC(2))]) is false
  not-defined("x", []) is true
  not-defined("x", [bind("z", numC(2)), bind("y", numC(3))]) is true
end

fun legal-id(id, reserved-names :: List) -> Bool:
  doc: "Takes id as a String or a List. Detremines if id is in reserved-keywords, and if id 
        has repeated elements. If any of these conditions are met, returns false; else returns 
        true."
  if String(id):
    not reserved-names.member(id)
  else if List(id):
    cases (List) id:
      | empty => true
      | link(front, rest) =>
        if reserved-names.member(front):
          false
        else:
          legal-id(rest, link(front, reserved-names))
        end
    end
  else:
    false
  end
where:
   legal-id(2, keywords) is false
   legal-id(["x", "x"], keywords) is false
   legal-id(["x", "y", "fun"], keywords) is false
   legal-id(["x", "y", "z"], keywords) is true
   legal-id("x", keywords) is true
end

fun lookup(s :: String, nv :: List<Env>) -> CFWAE-Value:
  doc: "Looks for s in environment nv and return its value, if any."
  cases (List<Env>) nv:
    | empty => raise("unbound identifier")
    | link(first, rest) =>
      if s == first.name:
        first.value
      else:
        lookup(s, rest)
      end
  end
end

fun p2(s): parse(read-sexpr(s));
#p2("((fun (x y) (* x y)) 2 3)")
#p2("((fun (self n) (self self n)) (fun (self n) (if0 n 0 (+ n (self self (- n 1))))) 10)")
#p2("((fun () 5) )")
#interp(p2("(with ((x 2) (y 3)) (with ((z (+ x y))) (+ x z)))"))
#interp(p2("(with ((f (fun () 0))) (f))"))
#interp(p2("((fun () 0))"))