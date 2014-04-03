#lang pyret/check

# cfwae.arr - Simple interpreter for CFWAE
# Copyright (C) 2014 - John Paul Gallegos Diaz <sylladie@gmail.com>

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

# Bindings map identifiers to values
data Binding:
  | bind (name :: String, value :: CFWAE)
end

# An Environment is a List<Binding>
mt-env = []
xtnd-env = link

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
  | closV (f :: CFWAE, e :: List<Binding>) # ExprC must be an fdC
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
        if args.length() == 1:
          raise("parse: unknown unary operator")
        else if args.length() == 2:
          if (op == "+") or (op == "-") or (op == "*") or (op == "/"):
            argL = list.index(args, 0)
            argR = list.index(args, 1)
            binopC(op, parse(argL), parse(argR))
          else if op == "with":
            w-bind = list.index(args, 0)
            w-body = list.index(args, 1)
            withC(create-bindings(w-bind, []), parse(w-body))
          else:
            raise("parse: unknown binary operator")
          end
        else if args.length() == 3:
          if op == "if0":
            argIf = list.index(args, 0)
            argThen = list.index(args, 1)
            argElse = list.index(args, 2)
            if0C(parse(argIf), parse(argThen), parse(argElse))
          else:
            raise("parse: unknown ternary operator")
          end
        else:
          raise("nothing")
        end
    end
  else:
    raise("parse: not number, list, or identifier")
  end
where:
  fun p(s): parse(read-sexpr(s)) end
#  p("3") is numC(3)
#  p("(+ 2 3)") is binopC("+", numC(2), numC(3))
#  p("(if0 0 1 2)") is if0C(numC(0), numC(1), numC(2))
#  p("(if0 1 2 3)") is if0C(numC(1), numC(2), numC(3))
  p("(with ((x 2) (y 3)) (+ x y))") is withC([bind("x", numC(2)), bind("y", numC(3))], binopC("+", idC("x"), idC("y")))
end

fun interp(e :: CFWAE, nv :: List<Binding>) -> CFWAE-Value:
  doc: "Execute the expression E, return the result of evaluation."
  cases (CFWAE) e:
    | numC(n) => numV(n)
    | binopC(op, l, r) =>
      if op == "+":
        plus-v(interp(l, nv), interp(r, nv))
      else if op == "-":
        sub-v(interp(l, nv), interp(r, nv))
      else if op == "*":
        mult-v(interp(l, nv), interp(r, nv))
      else:
        if r == 0:
          raise("Division by zero")
        else:
          div-v(interp(l, nv), interp(r, nv))
        end
      end
    | if0C(tst, thn, els) =>
      if interp(tst, nv) <> numV(0):
        interp(thn, nv)
      else:
        interp(els, nv)
      end
    | withC(bindList, body) =>
      interp(body, bindList)
    | idC(s) => lookup(s, nv)
  end
where:
  interp(if0C(numC(0), numC(1), numC(2)), []) is numV(2)
  interp(if0C(numC(1), numC(3), numC(2)), []) is numV(3)
  interp(withC([bind("x", numC(2)), bind("y", numC(3))], binopC("+", idC("x"), idC("y"))), []) is numV(5)
  interp(binopC("+", idC("x"), idC("y")), [bind("x", numC(2)), bind("y", numC(3))]) is numV(5)
end

# ---- Helper functions ----
  
# -- Arithmetic helper functions --

# Takes two numC values and returns a numV
fun plus-v(v1, v2): numV(v1.n + v2.n);
fun mult-v(v1, v2): numV(v1.n * v2.n);
fun sub-v(v1, v2): numV(v1.n - v2.n);
fun div-v(v1, v2): numV(v1.n / v2.n);

# -- Miscellaneous helper functions --
fun lookup(s :: String, nv :: List<Binding>) -> CFWAE:
  cases (List<Binding>) nv:
    | empty => raise("unbound identifier")
    | link(f, r) =>
      if s == f.name:
        f.value
      else:
        lookup(s, r)
      end
  end
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
end

fun create-bindings(lst :: List, bind-lst :: List<Binging>) -> List<Binding>:
  cases (List) lst:
    | empty => empty
    | link(front, rest) =>
      name = front.first
      expr = parse(front.rest.first)
      if not-defined(name, bind-lst):
        current-bind = bind(name, expr)
        xtnd-bind-list = link(current-bind, bind-lst)
        link(current-bind, create-bindings(rest, xtnd-bind-list))
      else:
        raise(name + " is defined twice")
      end
  end
where: 
  create-bindings(read-sexpr("((x 2) (y 3))"), []) is [bind("x", numC(2)), bind("y", numC(3))]
  create-bindings(read-sexpr("((x 2) (x 3))"), []) raises "x is defined twice"
end

check:
#  fun run(s): interp(parse(read-sexpr(s))) end
#  run("(if0 0 1 2)") is numV(2)
#  run("(if0 1 2 3)") is numV(2)
#  run("(if0 (- 1 1) 2 3)") is numV(3)
#  run("(if0 (+ 1 1) 2 3)") is numV(2)
end
