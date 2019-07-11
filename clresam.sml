fun paren s = "(" ^ s ^ ")"
fun pLn s = print (s ^ "\n")
fun list2string (f, l) =
    let
        val r = List.foldl (fn (e, r) =>
                               case r of
                                   NONE => SOME (f e)
                                 | SOME s => SOME (s ^ ", " ^ (f e))
                           ) NONE l
    in
        case r of
            NONE => "[]"
          | SOME r => "[" ^ r ^ "]"
    end
val counter = ref 0
fun newSym () =
    let
        val ret = "k" ^ (Int.toString (!counter))
        val _ = counter := ((!counter) + 1)
    in
        ret
    end



structure Func =
struct

datatype t = C of real
           | Var of string
           | Id
           | Limit of int * string * t
           | Pieces of (int * t) list
           | Fadd
           | Add
           | Mul
           | Pair of t * t
           | Left
           | Right
           | Circ of t * t

fun add2 (a, b) = Circ (Add, Pair (a, b))
fun mul2 (a, b) = Circ (Mul, Pair (a, b))
fun left e = Circ (Left, e)
fun right e = Circ (Right, e)

fun layoutFunc (C v, _) = Real.toString v
  | layoutFunc (Var x, _) = x
  | layoutFunc (Id, _) = "id"
  | layoutFunc (Limit (i, x, body), _) = "tab[" ^ x ^ " in " ^ (Int.toString i) ^ ": " ^ (layoutFunc (body, false)) ^ "]"
  | layoutFunc (Pieces l, _) =
    let
        val s = list2string (fn (len, f) => (Int.toString len) ^ " => " ^ (layoutFunc (f, false)), l)
    in
        "{" ^ s ^ "}"
    end
  | layoutFunc (Fadd, _) = "⊕"
  | layoutFunc (Add, _) = "addC"
  | layoutFunc (Mul, _) = "mulC"
  | layoutFunc (Pair (e1, e2), ifp) =
    let
        val s = (layoutFunc (e1, true)) ^ " △ " ^ (layoutFunc (e2, true))
    in
        if ifp then paren s else s
    end
  | layoutFunc (Left, ifp) = "exl"
  | layoutFunc (Right, ifp) = "exr"
  | layoutFunc (Circ (e1, e2), ifp) =
    let
        val s = (layoutFunc (e1, true)) ^ " ∘ " ^ (layoutFunc (e2, true))
    in
        if ifp then paren s else s
    end

fun layout func = layoutFunc (func, true)

fun subst (body, id, e) =
    let
        fun aux body =
            case body of
                (C v) => C v
              | Var y => if id = y then e else Var y
              | Id => Id
              | Limit (len, y, body) =>
                if id = y then Limit (len, y, body) else Limit (len, y, aux body)
              | Pieces l =>
                Pieces (List.map (fn (len, f) => (len, aux f)) l)
              | Fadd => Fadd
              | Add => Add
              | Mul => Mul
              | Pair (b1, b2) => Pair (subst (b1, id, e), subst (b2, id, e))
              | Left => Left
              | Right => Right
              | Circ (b1, b2) => Circ (subst (b1, id, e), subst (b2, id, e))
    in
        aux body
    end

fun calibrate (l1, l2) =
    case (l1, l2) of
        ([], l2) => raise Fail "length is not equal"
      | (l1, []) => raise Fail "length is not equal"
      | ((thr1, f1) :: t1, (thr2, f2) :: t2) =>
        if thr1 = thr2
        then (thr1, f1, f2) :: (calibrate (t1, t2))
        else if thr1 < thr2
        then (thr1, f1, f2) :: (calibrate (t1, (thr2, f2) :: t2))
        else (thr2, f1, f2) :: (calibrate ((thr1, f1) :: t1, t2))

fun eval (f, v: t) : t =
    let
        fun evalAdd (C a, C b) = C (a + b)
          | evalAdd (Pieces l1, Pieces l2) =
            let
                val l = calibrate (l1, l2)
                val l = List.map (fn (thr, f1, f2) => (thr, evalAdd (f1, f2))) l
            in
                Pieces l
            end
          | evalAdd (Limit (len1, x1, f1), Limit (len2, x2, f2)) =
            let
                val x = newSym ()
                val f1 = subst (f1, x1, Var x)
                val f2 = subst (f2, x2, Var x)
                val f = add2 (f1, f2)
            in
                Limit (len1, x, f)
            end
          | evalAdd (Pair (v11, v12), Pair (v21, v22)) = Pair (evalAdd (v11, v12), evalAdd (v21, v22))
          | evalAdd (a, b) = add2 (a, b)
        fun evalMul (C a, C b) = C (a * b)
          | evalMul (Pieces l1, Pieces l2) =
            let
                val l = calibrate (l1, l2)
                val l = List.map (fn (thr, f1, f2) => (thr, evalMul (f1, f2))) l
            in
                Pieces l
            end
          | evalMul (C a, Limit (len2, x2, f2)) = Limit (len2, x2, evalMul (C a, f2))
          | evalMul (Limit (len1, x1, f1), C b) = Limit (len1, x1, evalMul (f1, C b))
          | evalMul (Limit (len1, x1, f1), Limit (len2, x2, f2)) =
            let
                val x = newSym ()
                (* val _ = pLn (layout f1) *)
                val f1 = subst (f1, x1, Var x)
                (* val _ = pLn (layout f1) *)
                val f2 = subst (f2, x2, Var x)
                val f = mul2 (f1, f2)
            in
                Limit (len1, x, f)
            end
          | evalMul (Pair (v11, v12), Pair (v21, v22)) = Pair (evalMul (v11, v12), evalMul (v21, v22))
          | evalMul (a, b) = mul2 (a, b)
    in
        case (f, v) of
            (C v, _) => C v
          | (Id, v) => v
          | (Var x, _) => Var x
          | (Limit (len, x, body), v) => Limit (len, x, eval (body, v))
          | (Pieces l, v) =>
            let
                val v = case v of
                            C v => v
                          | _ => raise Fail "eval: bad pieces"
                val r = List.foldl (fn ((thr, f), r) =>
                                       case r of
                                           SOME r => SOME r
                                         | NONE =>
                                           if v < (Real.fromInt thr) then SOME f else NONE
                                   ) NONE l
            in
                case r of
                    NONE => raise Fail "eval: pieces out of scope"
                  | SOME f => eval (f, C v)
            end
          | (Fadd, Limit (len, x, body)) =>
            let
                val body = subst (body, x, Id)
                val base = List.tabulate (len, fn i => C (Real.fromInt i))
                val res = List.map (fn v => eval (body, v)) base
                val r = List.foldl (fn (e, r) =>
                                       case r of
                                           NONE => SOME e
                                         | SOME r => SOME (add2 (r, e))
                                   ) NONE res
            in
                case r of
                    NONE => raise Fail "eval: Fadd"
                  | SOME r => eval (r, v)
            end
          | (Add, Pair (a, b)) => evalAdd (a, b)
          | (Mul, Pair (a, b)) => evalMul (a, b)
          | (Pair (f1, f2), v) => Pair (eval (f1, v), eval (f2, v))
          | (Left, Pair (a, b)) => a
          | (Right, Pair (a, b)) => b
          | (Circ (f1, f2), v) => eval (f1, eval (f2, v))
          | _ => raise Fail ("eval: " ^ (layout f) ^ " in " ^  (layout v))
    end
fun pLnEval (f, v) =
    let
        val r = eval (f, v)
        val s = (layout f) ^ ": " ^ (layout v) ^ " -> " ^ (layout r)
    in
        pLn s
    end
fun pLnVec (Limit (len, x, body)) =
    let
        val body = subst (body, x, Id)
        val base = List.tabulate (len, fn i => C (Real.fromInt i))
        val res = List.map (fn v => eval (body, v)) base
        val s = list2string (layout, res)
    in
        pLn s
    end
  | pLnVec _ = raise Fail "pLnVec: not a vec"
end

structure D =
struct
structure F = Func
datatype t = Scale of F.t
           | Var of string
           | Add
           | Pair of t * t
           | Limit of int * string * t
           (* | Pieces of (int * t) list *)
           | Fadd
           | Left
           | Right
           | Circ of t * t

fun add2 (a, b) = Circ (Add, Pair (a, b))
fun left e = Circ (Left, e)
fun right e = Circ (Right, e)

fun layoutAux (Scale r, _) = F.layout r
  | layoutAux (Var x, _) = x
  | layoutAux (Limit (i, x, body), _) = "tab[" ^ x ^ " in " ^ (Int.toString i) ^ ": " ^ (layoutAux (body, false)) ^ "]"
  (* | layoutFunc (Pieces l, _) = *)
  (*   let *)
  (*       val s = list2string (fn (len, f) => (Int.toString len) ^ " => " ^ (layoutFunc (f, false))) l *)
  (*   in *)
  (*       "{" ^ s ^ "}" *)
  (*   end *)
  | layoutAux (Fadd, _) = "⊕"
  | layoutAux (Add, _) = "addD"
  | layoutAux (Pair (e1, e2), ifp) =
    let
        val s = (layoutAux (e1, true)) ^ " △ " ^ (layoutAux (e2, true))
    in
        if ifp then paren s else s
    end
  | layoutAux (Left, ifp) = "exl"
  | layoutAux (Right, ifp) = "exr"
  | layoutAux (Circ (e1, e2), ifp) =
    let
        val s = (layoutAux (e1, true)) ^ " ∘ " ^ (layoutAux (e2, true))
    in
        if ifp then paren s else s
    end
fun layout d = layoutAux (d, true)

fun subst (f, x, v) =
    let
        fun aux (Var y) = if x = y then v else Var y
          | aux (Pair (a, b)) = Pair (aux a, aux b)
          | aux (Limit (len, y, body)) = if x = y then Limit (len, y, body) else Limit (len, y, aux body)
          (* | Piece l => List.map (fn (len, f) => (len, aux f)) l *)
          | aux (Circ (a, b)) = Circ (aux a, aux b)
          | aux f = f
    in
        aux f
    end

fun evalCirc d =
    let
        fun evalScale (s, d) =
            let
                fun aux (Scale r) = Scale (F.eval (F.mul2 (r, s), F.C 0.0))
                  | aux (Pair (a, b)) = Pair (aux a, aux b)
                  | aux (Limit (len, x, body)) = Limit (len, x, aux body)
                  | aux _ = raise Fail "bad scale"
            in
                aux d
            end
        fun evalAdd (Scale a, Scale b) = Scale (F.eval (F.add2 (a, b), F.C 0.0))
          | evalAdd (Limit (len1, x1, body1), Limit (len2, x2, body2)) =
            let
                val x = newSym ()
                val f1 = subst (body1, x1, Var x)
                val f2 = subst (body2, x2, Var x)
                val f = evalAdd (f1, f2)
            in
                Limit (len1, x, f)
            end
          | evalAdd (Pair (v11, v12), Pair (v21, v22)) = Pair (evalAdd (v11, v12), evalAdd (v21, v22))
          | evalAdd (a, b) = add2 (a, b)
          (* | evalAdd (a, b) = raise Fail ("D:eval:evalAdd: " ^ (layoutAux (a, true)) ^ " + " ^ (layoutAux (b, true))) *)
        fun aux (Circ (d1, d2)) =
            (
              case (d1, aux d2) of
                  (Scale a, d) => evalScale (a, d)
                | (Add, Pair (a, b)) => evalAdd (a, b)
                | (Pair (a, b), c) => Pair (aux (Circ (a, c)), aux (Circ (b, c)))
                | (Limit (len, x, body), _) => Limit (len, x, aux body)
                | (Fadd, Scale (F.Limit (len, x, body))) =>
                  Scale (F.eval (F.Circ (F.Fadd, F.Limit (len, x, body)), F.C 0.0))
                | (Fadd, Scale (F.C r)) => Scale (F.C r)
                | (Left, Pair (a, b)) => a
                | (Right, Pair (a, b)) => b
                | (Circ (a, b), c) => aux (Circ (a, aux (Circ (b, c))))
                | (f1, f2) => Circ (f1, f2)
            )
          | aux (Pair (a, b)) = Pair (aux a, aux b)
          | aux (Limit (len, x, body)) = Limit (len, x, aux body)
          | aux x = x
    in
        aux d
    end
end

structure DPlus =
struct
open Func
structure D = D

fun ad f : (t -> D.t)=
    let
        fun aux (C r) : (t -> D.t)= (fn v => D.Scale (C 0.0))
          | aux (Var x) = (fn v => D.Scale (C 0.0))
          | aux Id = (fn v => D.Scale (C 1.0))
          | aux (Limit (len, x, body)) = (fn v => D.Limit (len, x, (aux body) v))
          | aux (Pieces l) =
            (fn v =>
                let
                    val v = case v of
                                C v => v
                              | _ => raise Fail "eval: bad pieces"
                    val r = List.foldl (fn ((thr, f), r) =>
                                           case r of
                                               SOME r => SOME r
                                             | NONE =>
                                               if v < (Real.fromInt thr) then SOME f else NONE
                                       ) NONE l
                in
                    case r of
                        NONE => raise Fail "DPlus: eval: pieces out of scope"
                      | SOME f => (aux f) (C v)
                end
            )
          | aux Fadd = (fn v => D.Fadd)
          | aux Add = (fn v => D.Add)
          | aux Mul =
            (fn v =>
                let
                    val (a, b) =
                        case v of
                            Pair (a, b) => (D.Scale a, D.Scale b)
                          (* | Pair (C a, Var b) => (D.Scale a, D.Var b) *)
                          (* | Pair (Var a, C b) => (D.Var a, D.Scale b) *)
                          (* | Pair (Var a, Var b) => (D.Var a, D.Var b) *)
                          | v => raise Fail ("ad:Mul:" ^ (layout v))
                in
                    D.add2 (D.Circ (a, D.Right), D.Circ (b, D.Left))
                end
            )
          | aux (Pair (f1, f2)) = (fn v => D.Pair ((aux f1) v, (aux f2) v))
          | aux Left = (fn v => D.Left)
          | aux Right = (fn v => D.Right)
          | aux (Circ (f1, f2)) =
            (fn v =>
                let
                    val v2 = eval (f2, v)
                    val d2 = (ad f2) v
                    val d1 = (ad f1) v2
                in
                    D.Circ (d1, d2)
                end
            )
    in
        aux f
    end
fun pLnDiff (f, v) =
    let
        val d = (ad f) v
        val s = (layout v) ^ " -> " ^ (D.layoutAux (D.evalCirc d, false)) ^ " = " ^ (D.layoutAux (d, false))
    in
        pLn s
    end
fun unfold (f, x) =
    let
         fun aux (Var y) = if y = x then Id else Var y
          | aux (Limit (len, y, body)) =
            if y = x
            then aux body
            else Limit (len, y, aux body)
          | aux (Pieces l) = Pieces (List.map (fn (len, f) => (len, aux f)) l)
          | aux (Pair (a, b)) = Pair (aux a, aux b)
          | aux (Circ (a, b)) = Circ (aux a, aux b)
          | aux a = a
    in
        aux f
    end

fun pLnDiffVec (f, g, x, len) =
    let
        val g' = unfold (g, x)
        val f' = Circ (f, g')
        val _ = pLn (layout g')
        val _ = pLn (layout f')
        fun aux v =
            case (D.evalCirc ((ad f') v), D.evalCirc ((ad g') v)) of
                (D.Scale (C r1), D.Scale (C r2)) => r1/r2
              | (a, b) => raise Fail ("not a Scale: " ^ (D.layoutAux (a, false)) ^ " / " ^ (D.layoutAux (b, false)))
        val base = List.tabulate (len, fn i => C (Real.fromInt i))
        val l = List.map aux base
    in
        pLn (list2string (Real.toString, l))
    end
end

open Func;
open DPlus;
let
    val fun1 = add2 (C 1.0, mul2 (C 2.0, Id))
    val _ = pLnEval (fun1, C 0.0)
    val _ = pLnEval (fun1, C 1.0)
    val _ = pLnEval (fun1, C 2.0)
    val _ = pLnDiff (fun1, C 0.0)
    val _ = pLnDiff (fun1, C 1.0)
    val _ = pLnDiff (fun1, C 2.0)
    val vec1 = Limit (6, "x", add2 (C 1.0, mul2 (C 2.0, Var "x")))
    val _ = pLn (layout vec1)
    val _ = pLnVec vec1
    val _ = pLnDiff (vec1, C 2.0)
    val elemwise = mul2 (Id, Id)
    val _ = pLn (layout elemwise)
    val fun2 = Circ (elemwise, fun1)
    val _ = pLnEval (fun2, C 0.0)
    val _ = pLnEval (fun2, C 1.0)
    val _ = pLnEval (fun2, C 2.0)
    val _ = pLnEval (elemwise, vec1)
    val _ = pLnDiff (fun2, C 0.0)
    val _ = pLnDiff (fun2, C 1.0)
    val _ = pLnDiff (fun2, C 2.0)
    val _ = pLnDiff (fun2, C 3.0)
    val _ = pLnDiff (fun2, C 4.0)
    val _ = pLnDiff (fun2, C 5.0)
    val _ = pLnVec (eval (elemwise, vec1))
    val dot = Circ (Fadd, mul2 (Id, Id))
    val _ = pLn (layout dot)
    val _ = pLnEval (dot, vec1)
    val fun3 = Circ (dot, fun1)
    val _ = pLnDiff (fun3, C 0.0)
    val _ = pLnDiff (fun3, C 1.0)
    val _ = pLnDiff (fun3, C 2.0)
    val fun4 = Pieces [(4, add2 (C 1.0, mul2 (C 2.0, Id))), (10, add2 (C 1.0, mul2 (C ~2.0, Id)))]
    val _ = List.map (fn e => pLnEval (fun4, e)) (List.tabulate (10, fn i => C (Real.fromInt i)))
    val vec2 = Limit (10, "x", Pieces [(4, add2 (C 1.0, mul2 (C 2.0, Var "x"))), (10, add2 (C 1.0, mul2 (C ~2.0, Var "x")))])
    val _ = pLn (layout vec2)
    val _ = pLnVec vec2
    val _ = pLnEval (dot, vec2)
    val _ = pLnDiffVec (dot, vec2, "x", 10)
in
    ()
end;
