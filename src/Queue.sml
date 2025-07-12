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
  
  fun rear (args as (m, xs, _, n, ys)) =
    if m >= n then front args
    else front (m + n, xs, rotate (Rev (0, xs, nil, ys, nil)), 0, nil)
  
  val empty = (0, nil, Idle, 0, nil)
  fun snoc ((m, xs, ys, n, zs), z) = rear (m, xs, ys, n + 1, z :: zs)
  fun uncons (m, x :: xs, ys, n, zs) = SOME (x, rear (m - 1, xs, discard ys, n, zs))
    | uncons _ = NONE
end

structure RealTimeQueue :> QUEUE =
struct
  datatype 'a state
    = Nil
    | ::: of 'a * 'a state ref
    | Step of 'a state * 'a list * 'a state ref
  
  (*  Both the front and the accumulator are fully forced streams.  *)
  fun step (x ::: r, y :: ys, zs) = x ::: ref (Step (!r, ys, ref (y ::: zs)))
    | step (_, _, r) = !r
  
  fun force r =
    case !r of
        Step xs => let val xs = step xs in r := xs; xs end
      | xs => xs
  
  type 'a queue = 'a state * 'a list * 'a state
  
  val empty = (Nil, nil, Nil)
  
  (*  When the schedule is empty, start the next rotation.  *)
  fun exec (args as (xs, ys, r)) =
    case force r of
        Nil => let val xs = step args in (xs, nil, xs) end
      | zs => (xs, ys, zs)
  
  fun snoc ((xs, ys, _ ::: zs), y) = exec (xs, y :: ys, zs)
    | snoc (_, x) = let val xs = x ::: ref Nil in (xs, nil, xs) end
  
  fun uncons (x ::: xs, ys, _ ::: zs) = SOME (x, exec (force xs, ys, zs))
    | uncons _ = NONE
end

structure BootstrappedQueue :> QUEUE =
struct
  datatype 'a state = Done of 'a list | Rev of 'a list
  
  fun force r =
    case !r of
        Done xs => xs
      | Rev xs => let val xs = rev xs in r := Done xs; xs end
  
  datatype 'a tree = Leaf of 'a | Node of 'a tree state ref
  
  fun delay xs = Node (ref (Rev xs))
  
  datatype 'a queue
    = Empty
    | Queue of int * 'a tree list * 'a queue * int * 'a tree list
  
  val empty = Empty
  fun pure x = Queue (1, x :: nil, Empty, 0, nil)
  fun front (m, xs, ys) = Queue (m, xs, ys, 0, nil)
  
  datatype 'a step
    = Snoc of 'a tree
    | Uncons
    | Rear1
    | Rear2 of int * 'a tree list
    | Front1
    | Front2 of int * int * 'a tree list
    | Return of 'a tree
  
  fun run (Empty, Snoc x :: ss) = run (pure x, ss)
    | run (Queue (m, xs, ys, n, zs), Snoc z :: ss) =
      run (Queue (m, xs, ys, n + 1, z :: zs), Rear1 :: ss)
    
    | run (Queue (m, x :: xs, ys, n, zs), Uncons :: ss) =
      run (Queue (m - 1, xs, ys, n, zs), Rear1 :: Front1 :: Return x :: ss)
    
    (*  Enforce the rear length invariant first.  *)
    | run (xyzs as Queue (m, xs, ys, n, zs), Rear1 :: ss) =
      if m >= n then
        run (xyzs, ss)
      else
        run (ys, Snoc (delay zs) :: Rear2 (m + n, xs) :: ss)
    
    | run (ys, Rear2 (m, xs) :: ss) = run (front (m, xs, ys), ss)
    
    (*  Enforce the nonempty front invariant only then.  *)
    | run (Queue (_, nil, Empty, _, _), Front1 :: ss) = run (Empty, ss)
    | run (Queue (m, nil, xs, n, ys), Front1 :: ss) =
      run (xs, Uncons :: Front2 (m, n, ys) :: ss)
    
    | run (xs, Front1 :: ss) = run (xs, ss)
    | run (ys, Return (Node xs) :: Front2 (m, n, zs) :: ss) =
      run (Queue (m, force xs, ys, n, zs), ss)
    
    | run args = args
  
  fun snoc (xs, x) = #1 (run (xs, Snoc (Leaf x) :: nil))
  
  fun uncons xs =
    case run (xs, Uncons :: nil) of
        (xs, Return (Leaf x) :: _) => SOME (x, xs)
      | _ => NONE
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
    | break (xs, (r, ys) :: ss) =
      let in
        r := Done xs;
        break (relink (xs, Q.uncons ys), ss)
      end
  
  fun tail (_ ::: xs) =
    case uncons xs of
        NONE => NONE
      | SOME xs => SOME (break (build (Relink xs, nil)))
end
