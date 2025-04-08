signature QUEUE =
sig
  type 'a queue
  
  val empty : 'a queue
  val snoc : 'a queue * 'a -> 'a queue
  val uncons : 'a queue -> ('a * 'a queue) option
end

signature CATENABLE =
sig
  type 'a cat
  
  val pure : 'a -> 'a cat
  val head : 'a cat -> 'a
  val tail : 'a cat -> 'a cat option
  val concat : 'a cat * 'a cat list -> 'a cat
end

structure HoodMelvilleQueue :> QUEUE =
struct
  datatype 'a state
    = Idle
    | Rev of int * 'a list * 'a list * 'a list * 'a list
    | App of int * 'a list * 'a list
    | Done of 'a list
  
  fun rotate (Rev (n, w :: ws, xs, y :: ys, zs)) = Rev (n + 1, ws, w :: xs, ys, y :: zs)
    | rotate (Rev (n, _, xs, y :: nil, ys)) = App (n, xs, y :: ys)
    | rotate (App (0, _, xs)) = Done xs
    | rotate (App (n, x :: xs, ys)) = App (n - 1, xs, x :: ys)
    | rotate xs = xs
  
  fun discard (Rev (n, ws, xs, ys, zs)) = Rev (n - 1, ws, xs, ys, zs)
    | discard (App (0, _, _ :: xs)) = Done xs
    | discard (App (n, xs, ys)) = App (n - 1, xs, ys)
    | discard xs = xs
  
  type 'a queue = int * 'a list * 'a state * int * 'a list
  
  fun front (m, xs, ys, n, zs) =
    case rotate ys of
        Done xs => (m, xs, Idle, n, zs)
      | ys => (m, xs, ys, n, zs)
  
  fun back (args as (m, xs, _, n, ys)) =
    if m >= n then front args
    else front (m + n, xs, rotate (Rev (0, xs, nil, ys, nil)), 0, nil)
  
  val empty = (0, nil, Idle, 0, nil)
  fun snoc ((m, xs, ys, n, zs), z) = back (m, xs, ys, n + 1, z :: zs)
  fun uncons (m, x :: xs, ys, n, zs) = SOME (x, back (m - 1, xs, discard ys, n, zs))
    | uncons _ = NONE
end

functor BootstrapQueue (Q : QUEUE) :> QUEUE =
struct
  datatype 'a state = Done of 'a list | Rev of 'a list
  
  fun force r =
    case !r of
        Done xs => xs
      | Rev xs => let val xs = rev xs in r := Done xs; xs end
  
  type 'a queue = int * 'a list * 'a state ref Q.queue * int * 'a list
  
  val empty = (0, nil, Q.empty, 0, nil)
  fun rotate (m, SOME (x, xs), n, ys) = (m, force x, xs, n, ys)
    | rotate _ = empty
  
  fun front (m, nil, xs, n, ys) = rotate (m, Q.uncons xs, n, ys)
    | front args = args
  
  fun back (args as (m, xs, ys, n, zs)) =
    if m >= n then front args
    else front (m + n, xs, Q.snoc (ys, ref (Rev zs)), 0, nil)
  
  fun snoc ((m, xs, ys, n, zs), z) = back (m, xs, ys, n + 1, z :: zs)
  fun uncons (m, x :: xs, ys, n, zs) = SOME (x, back (m - 1, xs, ys, n, zs))
    | uncons _ = NONE
end

functor Catenable (Q : QUEUE) :> CATENABLE =
struct
  open Q
  
  datatype 'a state
    = Done of 'a
    | Concat of 'a * 'a list
    | Relink of 'a state ref * 'a state ref queue
  
  datatype 'a cat = ::: of 'a * 'a cat state ref queue
  
  fun pure x = x ::: empty
  fun head (x ::: _) = x
  fun link (x ::: xs, ys) = x ::: snoc (xs, ref ys)
  
  fun concat (xs, nil) = xs
    | concat (xs, y :: ys) = link (xs, Concat (y, ys))
  
  fun relink (xs, NONE) = xs
    | relink (xs, SOME ys) = link (xs, Relink ys)
  
  fun build (Done xs, ss) = (xs, ss)
    | build (Concat xs, ss) = (concat xs, ss)
    | build (Relink (r, xs), ss) = build (!r, (r, xs) :: ss)
  
  fun break (xs, nil) = xs
    | break (xs, (r, ys) :: ss) = (r := Done xs; break (relink (xs, Q.uncons ys), ss))
  
  fun tail (_ ::: xs) =
    case uncons xs of
        NONE => NONE
      | SOME xs => SOME (break (build (Relink xs, nil)))
end
