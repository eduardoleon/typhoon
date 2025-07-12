structure SplayTree :> SEARCH_TREE =
struct
  datatype 'a tree = Empty | Tree of 'a tree * 'a * 'a tree
  
  val empty = Empty
  fun pure x = Tree (Empty, x, Empty)
  
  fun l3 (a,x,b,y,c) = Tree (a, x, Tree (b,y,c))
  fun r3 (a,x,b,y,c) = Tree (Tree (a,x,b), y, c)
  fun l4 (a,x,b,y,c,z,d) = Tree (a, x, l3 (b,y,c,z,d))
  fun r4 (a,x,b,y,c,z,d) = Tree (r3 (a,x,b,y,c), z, d)
  
  datatype 'a move = L of 'a * 'a tree | R of 'a tree * 'a | T
  
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
  
  type 'a leaf = 'a move list
  type 'a hole = 'a tree * 'a tree * 'a move list
  
  fun splay ss = upd (Empty, ss)
  fun update (x, (a, b, ss)) = upd (Tree (a,x,b), ss)
  fun insert (x, ss) = upd (pure x, ss)
  val delete = cut
  
  datatype 'a focus = Leaf of 'a leaf | Node of 'a * 'a hole
  
  fun focus (Empty, ss) = Leaf ss
    | focus (Tree (a, x, b), ss) = Node (x, (a, b, ss))
  
  fun root xs = focus (xs, nil)
  fun left (x, (a, b, ss)) = focus (a, L (x, b) :: ss)
  fun right (x, (a, b, ss)) = focus (b, R (a, x) :: ss)
  fun prune (a, b, _) = (a, b, nil)
  
  fun cut (Tree (a,x,b), ss) = cut (b, R (a,x) :: ss)
    | cut (Empty, ss) = ss
  
  fun ins (c, R (b,y) :: T :: R (a,x) :: ss) = ins (r3 (a,x,b,y,c), ss)
    | ins (xs, nil) = cut (xs, nil)
    | ins (xs, ss) = cut (xs, T :: ss)
  
  fun upd (b, R (a,x) :: ss) = upd (Tree (a,x,b), ss)
    | upd (xs, T :: ss) = upd (xs, ss)
    | upd (xs, _) = xs
  
  fun all (x :: xs, ss) = all (xs, ins (pure x, ss))
    | all (nil, ss) = upd (Empty, ss)
  
  fun fromAsc xs = all (xs, nil)
  
  fun cut (Tree (a,x,b), ss) = cut (a, L (x,b) :: ss)
    | cut (Empty, ss) = ss
  
  fun ins (a, L (x,b) :: T :: L (y,c) :: ss) = ins (l3 (a,x,b,y,c), ss)
    | ins (xs, nil) = cut (xs, nil)
    | ins (xs, ss) = cut (xs, T :: ss)
  
  fun upd (a, L (x,b) :: ss) = upd (Tree (a,x,b), ss)
    | upd (xs, T :: ss) = upd (xs, ss)
    | upd (xs, _) = xs
  
  fun all (x :: xs, ss) = all (xs, ins (pure x, ss))
    | all (nil, ss) = upd (Empty, ss)
  
  fun fromDesc xs = all (xs, nil)
  
  datatype 'a chunk = One of 'a | Many of 'a tree
  
  fun loop (xs, nil) = xs
    | loop (xs, One x :: ss) = loop (x :: xs, ss)
    | loop (xs, Many Empty :: ss) = loop (xs, ss)
    | loop (xs, Many (Tree (a, x, b)) :: ss) = loop (xs, Many b :: One x :: Many a :: ss)
  
  fun toAsc xs = loop (nil, Many xs :: nil)
  
  fun loop (xs, nil) = xs
    | loop (xs, One x :: ss) = loop (x :: xs, ss)
    | loop (xs, Many Empty :: ss) = loop (xs, ss)
    | loop (xs, Many (Tree (a, x, b)) :: ss) = loop (xs, Many a :: One x :: Many b :: ss)
  
  fun toDesc xs = loop (nil, Many xs :: nil)
end
