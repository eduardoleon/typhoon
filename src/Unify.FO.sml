signature FIRST_ORDER =
sig
  type term
  
  datatype view
    = Var of int
    | Apply of int * term list

  val var : int -> term
  val apply : int * term list -> term
  
  val view : term -> view
  val free : term -> term list
  val unify : term * term -> bool
end

structure FirstOrder :> FIRST_ORDER =
struct
  datatype state
    = Var' of int
    | Apply' of int * term list
    | Child of term
  
  withtype term = state ref
  
  fun var n = ref (Var' n)
  fun apply xs = ref (Apply' xs)
  
  datatype view
    = Var of int
    | Apply of int * term list
  
  fun loop (r, s) =
    case !s of
        Var' n => (s, Var n)
      | Apply' xs => (s, Apply xs)
      | Child t => (r := Child t; loop (s, t))
  
  fun root r = loop (r, r)
  fun view r = #2 (root r)
  
  fun loop (x, xs, nil) = x :: xs
    | loop (x, xs, y :: ys) = if x = y then xs else loop (x, xs, ys)
  
  fun x ::: xs = loop (x, xs, xs)
  
  fun loop (xs, nil) = xs
    | loop (xs, nil :: yss) = loop (xs, yss)
    | loop (xs, (y :: ys) :: yss) =
      case view y of
          Var _ => loop (y ::: xs, ys :: yss)
        | Apply (_, zs) => loop (xs, zs :: ys :: yss)
  
  fun free x = loop (nil, (x :: nil) :: nil)
  
  fun loop (r, _, s, nil) = (r := Child s; true)
    | loop (r, n, s, nil :: xss) = loop (r, n, s, xss)
    | loop (r, n, s, (x :: xs) :: xss) =
      let
        val (t, v) = root x
        val xss = xs :: xss
      in
        (r <> t) andalso
        case v of
            Var m => (t := Var' (Int.min (m, n)); loop (r, n, s, xss))
          | Apply (_, xs) => loop (r, n, s, xs :: xss)
      end
  
  fun assign (r, n, s) = loop (r, n, s, (s :: nil) :: nil)
  
  fun loop ((x :: xs, y :: ys) :: xss) =
      let
        val (r, v) = root x
        val (s, w) = root y
        val xss = (xs, ys) :: xss
      in
        if r = s then
          loop xss
        else
          case (v, w) of
              (Var n, _) => assign (r, n, s) andalso loop xss
            | (_, Var n) => assign (s, n, r) andalso loop xss
            | (Apply (m, xs), Apply (n, ys)) =>
              m = n andalso length xs = length ys andalso loop ((xs, ys) :: xss)
      end
    
    | loop (_ :: xss) = loop xss
    | loop nil = true
  
  fun unify (x, y) = loop ((x :: nil, y :: nil) :: nil)
end
