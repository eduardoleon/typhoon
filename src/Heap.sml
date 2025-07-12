signature ORDERED =
sig
  type elem
  
  val <= : elem * elem -> bool
end

signature BASIC_HEAP =
sig
  type elem
  type heap
  
  val empty : heap
  val cons : elem * heap -> heap
  val uncons : heap -> (elem * heap) option
  val unsnoc : heap -> (heap * elem) option
end

signature HEAP =
sig
  type elem
  type heap
  
  val pure : elem -> heap
  val head : heap -> elem
  val tail : heap -> heap option
  val link : heap * heap -> heap
end

functor SplayHeap (E : ORDERED) :> BASIC_HEAP where type elem = E.elem =
struct
  open E
  
  datatype heap = Empty | Node of heap * elem * heap
  
  val empty = Empty
  
  fun l3 (a,x,b,y,c) = Node (a, x, Node (b,y,c))
  fun r3 (a,x,b,y,c) = Node (Node (a,x,b), y, c)
  fun l4 (a,x,b,y,c,z,d) = Node (a, x, l3 (b,y,c,z,d))
  fun r4 (a,x,b,y,c,z,d) = Node (r3 (a,x,b,y,c), z, d)
  
  datatype step = L of elem * heap | R of heap * elem
  
  fun merge (Node (a,x,b), L (y,c) :: L (z,d) :: ss) = merge (l4 (a,x,b,y,c,z,d), ss)
    | merge (Node (c,z,d), R (b,y) :: R (a,x) :: ss) = merge (r4 (a,x,b,y,c,z,d), ss)
    | merge (Node (a,x,b), L (y,c) :: ss) = merge (l3 (a,x,b,y,c), ss)
    | merge (Node (b,y,c), R (a,x) :: ss) = merge (r3 (a,x,b,y,c), ss)
    | merge (xs, _) = xs
  
  fun split (p, Empty, ss) = merge (Node (Empty, p, Empty), ss)
    | split (p, Node (a,x,b), ss) =
      if p <= x then split (p, a, L (x,b) :: ss)
                else split (p, b, R (a,x) :: ss)
  
  fun cons (x, xs) = split (x, xs, nil)
  
  fun merge (a, (x,b) :: (y,c) :: ss) = merge (l3 (a,x,b,y,c), ss)
    | merge (a, (x,b) :: nil) = Node (a,x,b)
    | merge (xs, nil) = xs
  
  fun split (Node (a,x,b), ss) = split (a, (x,b) :: ss)
    | split (Empty, (x, xs) :: ss) = SOME (x, merge (xs, ss))
    | split (Empty, nil) = NONE
  
  fun uncons xs = split (xs, nil)
  
  fun merge (c, (b,y) :: (a,x) :: ss) = merge (r3 (a,x,b,y,c), ss)
    | merge (b, (a,x) :: nil) = Node (a,x,b)
    | merge (xs, nil) = xs
  
  fun split (Node (a,x,b), ss) = split (b, (a,x) :: ss)
    | split (Empty, (xs, x) :: ss) = SOME (merge (xs, ss), x)
    | split (Empty, nil) = NONE
  
  fun unsnoc xs = split (xs, nil)
end

functor PairingHeap (E : ORDERED) :> HEAP where type elem = E.elem =
struct
  open E
  
  datatype heap = ::: of elem * heap list
  
  fun pure x = x ::: nil
  fun head (x ::: _) = x
  fun comp (x ::: _, y ::: _) = x <= y
  fun link (ys as x ::: xss, xs as y ::: yss) =
    if x <= y then x ::: xs :: xss
              else y ::: ys :: yss
  
  fun sweep (x :: y :: xs) = sweep (link (y, x) :: xs)
    | sweep (x :: nil) = SOME x
    | sweep nil = NONE
  
  fun pair (x :: y :: xs, ys) = pair (xs, link (x, y) :: ys)
    | pair (x :: nil, xs) = sweep (x :: xs)
    | pair (nil, xs) = sweep xs
  
  fun tail (_ ::: xs) = pair (xs, nil)
end

functor LazyPairingHeap (E : ORDERED) :> HEAP where type elem = E.elem =
struct
  open E
  
  datatype 'a state
    = Done of 'a
    | Pair of 'a * 'a * 'a state ref option
  
  datatype heap = Heap of elem * heap state ref option * heap option
  
  fun pure x = Heap (x, NONE, NONE)
  fun head (Heap (x, _, _)) = x
  fun comp (Heap (x, _, _), Heap (y, _, _)) = x <= y
  fun cons (Heap (x, xs, NONE), ys) = Heap (x, xs, SOME ys)
    | cons (Heap (x, xs, SOME ys), zs) = Heap (x, SOME (ref (Pair (ys, zs, xs))), NONE)
  
  fun link (xs, ys) = if comp (xs, ys) then cons (xs, ys) else cons (ys, xs)
  
  datatype step = Link of heap * heap | Memo of heap state ref
  
  fun build (Done x, ss) = (x, ss)
    | build (Pair (x, y, NONE), ss) = (link (x, y), ss)
    | build (Pair (x, y, SOME r), ss) = build (!r, Memo r :: Link (x, y) :: ss)
  
  fun break (xs, nil) = xs
    | break (xs, Memo r :: ss) = (r := Done xs; break (xs, ss))
    | break (xs, Link ys :: ss) = break (link (xs, link ys), ss)
  
  fun force r = break (build (!r, Memo r :: nil))
  fun tail (Heap (_, NONE, NONE)) = NONE
    | tail (Heap (_, NONE, SOME xs)) = SOME xs
    | tail (Heap (_, SOME xs, NONE)) = SOME (force xs)
    | tail (Heap (_, SOME xs, SOME ys)) = SOME (link (force xs, ys))
end
