structure RedBlackTree :> SEARCH_TREE =
struct
  datatype 'a tree
    = Empty
    | Red of 'a tree * 'a * 'a tree
    | Black of 'a tree * 'a * 'a tree
  
  val empty = Empty
  fun pure x = Red (Empty, x, Empty)
  
  fun l2 ((a,x,b),y,c) = Red (a, x, Red (b,y,c))
  fun r2 (a,x,(b,y,c)) = Red (Red (a,x,b), y, c)
  
  fun l3 (a,x,b,y,c) = Red (Black a, x, Black (b,y,c))
  fun r3 (a,x,b,y,c) = Red (Black (a,x,b), y, Black c)
  fun m3 (a,x,(b,y,c),z,d) = Red (Black (a,x,b), y, Black (c,z,d))
  
  fun u3 (Red a,x,b,y,c) = l3 (a,x,b,y,c)
    | u3 (a,x,b,y,Red c) = r3 (a,x,b,y,c)
    | u3 (a,x,b,y,c) = Black (a, x, Red (b,y,c))
  
  (*  Our zipper type is based on the following tree representation:
   *  
   *    datatype 'a tree
   *      = Leaf
   *      | Thin of 'a tree
   *      | Node of 'a tree * 'a * 'a tree
   *  
   *  In this representation, nodes are intrinsically red, but can be blackened with
   *  a thin wrapper.  In other words, the conversion function is
   *  
   *    fun conv Empty = Leaf
   *      | conv (Red (a,x,b)) = Node (conv a, x, conv b)
   *      | conv (Black (a,x,b)) = Thin (Node (conv a, x, conv b))
   *)
  datatype 'a step = L of 'a * 'a tree | R of 'a tree * 'a | T
  
  fun upd (Red xs, T :: ss) = upd (Black xs, ss)
    | upd (a, L (x,b) :: ss) = upd (Red (a,x,b), ss)
    | upd (b, R (a,x) :: ss) = upd (Red (a,x,b), ss)
    | upd (xs, _) = xs
  
  (*  After inserting, the focused node might be too tall to be directly merged with
   *  its context.  In this case, we rotate outward from the focused node, pushing
   *  one child onto its sibling.
   *)
  fun ins (Red a, L (x,b) :: L (y,c) :: T :: ss) = ins (l3 (a,x,b,y,c), ss)
    | ins (Red b, R (a,x) :: L (y,c) :: T :: ss) = ins (m3 (a,x,b,y,c), ss)
    | ins (Red b, L (y,c) :: R (a,x) :: T :: ss) = ins (m3 (a,x,b,y,c), ss)
    | ins (Red c, R (b,y) :: R (a,x) :: T :: ss) = ins (r3 (a,x,b,y,c), ss)
    | ins (Red xs, nil) = Black xs
    | ins xs = upd xs
  
  (*  Deleting an arbitrary node is a three-phase operation:
   *  
   *  -  Rotate the focused node downward until it is a leaf.
   *  -  Rebuild the tree up to the original position of the focused node.
   *  -  Rebuild the remainder of the tree.
   *)
  
  (*  During the third phase, the focused node might be too short to be directly merged
   *  with its context.  In this case, we rotate inward into the focused node, pulling
   *  one descendant from its sibling.
   *)
  fun del (Red xs, T :: ss) = del (Black xs, ss)
    | del (a, T :: L (x, Red (b,y,c)) :: ss) = del (a, T :: L (x,b) :: L (y,c) :: ss)
    | del (c, T :: R (Red (a,x,b), y) :: ss) = del (c, T :: R (b,y) :: R (a,x) :: ss)
    | del (a, T :: L (x, Black (Red b,y,c)) :: ss) = upd (m3 (a,x,b,y,c), ss)
    | del (c, T :: R (Black (a,x,Red b), y) :: ss) = upd (m3 (a,x,b,y,c), ss)
    | del (a, T :: L (x, Black b) :: ss) = del (r2 (a,x,b), T :: ss)
    | del (b, T :: R (Black a, x) :: ss) = del (l2 (a,x,b), T :: ss)
    | del xs = upd xs
  
  (*  During the second phase, the context is in a broken state for reasons explained
   *  below.  If the focused node is as tall as the one it replaces, then we restore
   *  its ancestors to their original state.  Otherwise, we rotate inward into the
   *  focused node, pulling one descendant from its nearest black ancestor.
   *)
  fun sew (Red b, L (y,c) :: R (a,x) :: T :: ss) = sew (m3 (a,x,b,y,c), ss)
    | sew (Red a, L (x,b) :: ss) = sew (l2 (a,x,b), ss)
    | sew (Red b, R (a,x) :: ss) = sew (r2 (a,x,b), ss)
    | sew (b, L (y,c) :: R (a,x) :: T :: ss) = sew (u3 (a,x,b,y,c), ss)
    | sew (a, L (x,b) :: ss) = sew (Red (a,x,b), ss)
    | sew (b, R (a,x) :: ss) = sew (Red (a,x,b), ss)
    | sew (xs, _) = xs
  
  (*  During the first phase, we have two focused descendants of the original node,
   *  whose black height must remain equal at all times.  Therefore, we must descend
   *  from black nodes in tandem, and we keep track of when we do so.
   *)
  fun cut (Black (a,x,b), Black (c,y,d), ss) = cut (b, c, L (y,d) :: R (a,x) :: T :: ss)
    | cut (a, Red (b,x,c), ss) = cut (a, b, L (x,c) :: ss)
    | cut (Red (a,x,b), c, ss) = cut (b, c, R (a,x) :: ss)
    | cut (xs, _, ss) = sew (xs, ss)
  
  type 'a leaf = 'a step list
  type 'a hole = 'a tree * 'a tree * 'a step list
  
  fun splay ss = upd (Empty, ss)
  fun update (x, (a, b, ss)) = upd (Red (a,x,b), ss)
  fun insert (x, ss) = ins (pure x, ss)
  fun delete (a, b, ss) = del (cut (a, b, nil), ss)
  
  datatype 'a focus = Leaf of 'a leaf | Node of 'a * 'a hole
  
  fun focus (Empty, ss) = Leaf ss
    | focus (Red (a,x,b), ss) = Node (x, (a, b, ss))
    | focus (Black (a,x,b), ss) = Node (x, (a, b, T :: ss))
  
  fun root xs = focus (xs, nil)
  fun left (x, (a, b, ss)) = focus (a, L (x,b) :: ss)
  fun right (x, (a, b, ss)) = focus (b, R (a,x) :: ss)
  fun prune (a, b, _) = (a, b, T :: nil)
  
  (*  To build a red-black tree from a sorted list, we work with zippers focused on
   *  the rightmost leaf, satisfying the additional invariant that the entire path
   *  to this leaf consists of black nodes only.
   *  
   *  Inserting a single element is a two-phase operation:
   *  
   *  -  Ascend the tree to restore the aforementioned invariant.
   *  -  Descend the tree to refocus on the rightmost leaf.
   *)
  
  (*  During the second phase, we do not insert black markers, because we know in
   *  advance that every node in our path ought to be black.
   *)
  fun cut (Red (a,x,b), ss) = cut (b, R (a,x) :: ss)
    | cut (_, ss) = ss
  
  (*  During the first phase, if the focused node has a red sibling, then we turn
   *  it black and refocus on its parent, which has just become red to preserve
   *  the black height invariant.  Otherwise, a single outward rotation suffices
   *  to rebalance the tree, so we move on to the second phase.
   *)
  fun ins (b, R (Red a, x) :: ss) = ins (Red (Black a, x, b), ss)
    | ins (Red b, R (a,x) :: ss) = cut (r2 (a,x,b), ss)
    | ins xs = cut xs
  
  fun upd (b, R (a,x) :: ss) = upd (Black (a,x,b), ss)
    | upd (xs, _) = xs
  
  fun all (x :: xs, ss) = all (xs, ins (pure x, ss))
    | all (nil, ss) = upd (Empty, ss)
  
  fun fromAsc xs = all (xs, nil)
  
  (*  To build a tree from a descendingly sorted list, we use the same algorithm
   *  as in the ascending case, except we now work with zippers focused on the
   *  leftmost, rather than rightmost leaf.
   *)
  
  fun cut (Red (a,x,b), ss) = cut (a, L (x,b) :: ss)
    | cut (_, ss) = ss
  
  fun ins (a, L (x, Red b) :: ss) = ins (Red (a, x, Black b), ss)
    | ins (Red a, L (x,b) :: ss) = cut (l2 (a,x,b), ss)
    | ins xs = cut xs
  
  fun upd (a, L (x,b) :: ss) = upd (Black (a,x,b), ss)
    | upd (xs, _) = xs
  
  fun all (x :: xs, ss) = all (xs, ins (pure x, ss))
    | all (nil, ss) = upd (Empty, ss)
  
  fun fromDesc xs = all (xs, nil)
  
  (*  To build a list from a tree, we work with chunks consisting of one or several
   *  elements.  A single element can be directly shifted to the final list, whereas
   *  a chunk of many elements is further split into subchunks.
   *)
  datatype 'a step = One of 'a | Many of 'a tree
  
  fun loop (xs, nil) = xs
    | loop (xs, One x :: ss) = loop (x :: xs, ss)
    | loop (xs, Many Empty :: ss) = loop (xs, ss)
    | loop (xs, Many (Red (a, x, b)) :: ss) = loop (xs, Many b :: One x :: Many a :: ss)
    | loop (xs, Many (Black (a, x, b)) :: ss) = loop (xs, Many b :: One x :: Many a :: ss)
  
  fun toAsc xs = loop (nil, Many xs :: nil)
  
  fun loop (xs, nil) = xs
    | loop (xs, One x :: ss) = loop (x :: xs, ss)
    | loop (xs, Many Empty :: ss) = loop (xs, ss)
    | loop (xs, Many (Red (a, x, b)) :: ss) = loop (xs, Many a :: One x :: Many b :: ss)
    | loop (xs, Many (Black (a, x, b)) :: ss) = loop (xs, Many a :: One x :: Many b :: ss)
  
  fun toDesc xs = loop (nil, Many xs :: nil)
  
  datatype 'a step = R | B | T of 'a tree
  
  fun loop (ns, T Empty :: ss) = loop (0 :: ns, ss)
    | loop (ns, T (Red (a,_,b)) :: ss) = loop (ns, T a :: T b :: R :: ss)
    | loop (ns, T (Black (a,_,b)) :: ss) = loop (ns, T a :: T b :: B :: ss)
    | loop (m :: n :: ns, R :: ss) = if m = n then loop (n :: ns, ss) else ~1
    | loop (m :: n :: ns, B :: ss) = if m = n then loop (n + 1 :: ns, ss) else ~1
    | loop (n :: nil, nil) = n
    | loop _ = ~1
  
  fun height xs = loop (nil, T xs :: nil)
end
