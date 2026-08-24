structure SplayTree :> SEARCH_TREE =
struct
  datatype 'a tree = Empty | Tree of 'a tree * 'a * 'a tree
  
  val empty = Empty
  fun pure x = Tree (Empty, x, Empty)
  
  fun l3 (a,x,b,y,c) = Tree (a, x, Tree (b,y,c))
  fun r3 (a,x,b,y,c) = Tree (Tree (a,x,b), y, c)
  fun l4 (a,x,b,y,c,z,d) = Tree (a, x, l3 (b,y,c,z,d))
  fun r4 (a,x,b,y,c,z,d) = Tree (r3 (a,x,b,y,c), z, d)
  
  datatype 'a step = L of 'a * 'a tree | R of 'a tree * 'a | T
  
  fun upd (Tree (a,x,b), L (y,c) :: L (z,d) :: ss) = upd (l4 (a,x,b,y,c,z,d), ss)
    | upd (Tree (c,z,d), R (b,y) :: R (a,x) :: ss) = upd (r4 (a,x,b,y,c,z,d), ss)
    | upd (Tree (a,x,b), L (y,c) :: ss) = upd (l3 (a,x,b,y,c), ss)
    | upd (Tree (b,y,c), R (a,x) :: ss) = upd (r3 (a,x,b,y,c), ss)
    | upd (a, L (x,b) :: ss) = upd (Tree (a,x,b), ss)
    | upd (b, R (a,x) :: ss) = upd (Tree (a,x,b), ss)
    | upd (xs, _) = xs
  
  fun cut (Tree (a,x,b), Tree (c,y,d), ss) = cut (b, c, L (y,d) :: R (a,x) :: ss)
    | cut (xs, Empty, ss) = upd (xs, ss)
    | cut (Empty, xs, ss) = upd (xs, ss)
  
  type 'a leaf = 'a step list
  type 'a hole = 'a tree * 'a tree * 'a step list
  
  fun restore ss = upd (Empty, ss)
  fun update (x, (a, b, ss)) = upd (Tree (a,x,b), ss)
  fun insert (x, ss) = upd (pure x, ss)
  val delete = cut
  
  datatype 'a focus = Leaf of 'a leaf | Node of 'a * 'a hole
  
  fun focus (Empty, ss) = Leaf ss
    | focus (Tree (a, x, b), ss) = Node (x, (a, b, ss))
  
  fun root xs = focus (xs, nil)
  fun left (x, (a, b, ss)) = focus (a, L (x, b) :: ss)
  fun right (x, (a, b, ss)) = focus (b, R (a, x) :: ss)
  
  type 'a build_asc = 'a step list ref
  type 'a build_desc = 'a step list ref
  
  fun cut (Tree (a,x,b), ss) = cut (b, R (a,x) :: ss)
    | cut (Empty, ss) = ss
  
  fun ins (c, R (b,y) :: T :: R (a,x) :: ss) = ins (r3 (a,x,b,y,c), ss)
    | ins (xs, nil) = cut (xs, nil)
    | ins (xs, ss) = cut (xs, T :: ss)
  
  fun upd (b, R (a,x) :: ss) = upd (Tree (a,x,b), ss)
    | upd (xs, T :: ss) = upd (xs, ss)
    | upd (xs, _) = xs
  
  fun fromAsc () = ref nil
  fun putAsc (r, x) = r := ins (pure x, !r)
  fun buildAsc r = upd (Empty, !r)
  
  fun cut (Tree (a,x,b), ss) = cut (a, L (x,b) :: ss)
    | cut (Empty, ss) = ss
  
  fun ins (a, L (x,b) :: T :: L (y,c) :: ss) = ins (l3 (a,x,b,y,c), ss)
    | ins (xs, nil) = cut (xs, nil)
    | ins (xs, ss) = cut (xs, T :: ss)
  
  fun upd (a, L (x,b) :: ss) = upd (Tree (a,x,b), ss)
    | upd (xs, T :: ss) = upd (xs, ss)
    | upd (xs, _) = xs
  
  fun fromDesc () = ref nil
  fun putDesc (r, x) = r := ins (pure x, !r)
  fun buildDesc r = upd (Empty, !r)
  
  datatype 'a chunk = One of 'a | Many of 'a tree
  
  type 'a iter_asc = 'a chunk list ref
  type 'a iter_desc = 'a chunk list ref
  
  fun loop (_, nil) = NONE
    | loop (r, One x :: ss) = SOME x before r := ss
    | loop (r, Many Empty :: ss) = loop (r, ss)
    | loop (r, Many (Tree (a,x,b)) :: ss) = loop (r, Many a :: One x :: Many b :: ss)
  
  fun toAsc xs = ref (Many xs :: nil)
  fun nextAsc r = loop (r, !r)
  
  fun loop (_, nil) = NONE
    | loop (r, One x :: ss) = SOME x before r := ss
    | loop (r, Many Empty :: ss) = loop (r, ss)
    | loop (r, Many (Tree (a,x,b)) :: ss) = loop (r, Many b :: One x :: Many a :: ss)
  
  fun toDesc xs = ref (Many xs :: nil)
  fun nextDesc r = loop (r, !r)
end
