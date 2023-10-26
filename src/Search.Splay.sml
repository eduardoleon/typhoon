structure SplayTree :> SEARCH_TREE =
struct
  datatype 'a tree = Empty | Tree of 'a tree * 'a * 'a tree
  
  val empty = Empty
  fun pure x = Tree (Empty, x, Empty)
  
  fun l3 (a,x,b,y,c) = Tree (a, x, Tree (b,y,c))
  fun r3 (a,x,b,y,c) = Tree (Tree (a,x,b), y, c)
  fun l4 (a,x,b,y,c,z,d) = Tree (a, x, l3 (b,y,c,z,d))
  fun r4 (a,x,b,y,c,z,d) = Tree (r3 (a,x,b,y,c), z, d)
  
  datatype 'a step = L of 'a * 'a tree | R of 'a tree * 'a
  
  fun upd (Tree (a,x,b), L (y,c) :: L (z,d) :: ss) = upd (l4 (a,x,b,y,c,z,d), ss)
    | upd (Tree (c,z,d), R (b,y) :: R (a,x) :: ss) = upd (r4 (a,x,b,y,c,z,d), ss)
    | upd (Tree (a,x,b), L (y,c) :: ss) = upd (l3 (a,x,b,y,c), ss)
    | upd (Tree (b,y,c), R (a,x) :: ss) = upd (r3 (a,x,b,y,c), ss)
    | upd (a, L (x,b) :: ss) = upd (Tree (a,x,b), ss)
    | upd (b, R (a,x) :: ss) = upd (Tree (a,x,b), ss)
    | upd (xs, nil) = xs
  
  fun cut (Tree (a,x,b), Tree (c,y,d), ss) = cut (b, c, L (y,d) :: R (a,x) :: ss)
    | cut (xs, Empty, ss) = upd (xs, ss)
    | cut (Empty, xs, ss) = upd (xs, ss)
  
  type 'a leaf = 'a step list
  type 'a hole = 'a tree * 'a tree * 'a step list
  
  fun splay ss = upd (Empty, ss)
  fun update (x, (a, b, ss)) = upd (Tree (a, x, b), ss)
  fun insert (x, ss) = upd (pure x, ss)
  val delete = cut
  
  datatype 'a focus = Leaf of 'a leaf | Node of 'a * 'a hole
  
  fun focus (Empty, ss) = Leaf ss
    | focus (Tree (a, x, b), ss) = Node (x, (a, b, ss))
  
  fun root xs = focus (xs, nil)
  fun left (x, (a, b, ss)) = focus (a, L (x, b) :: ss)
  fun right (x, (a, b, ss)) = focus (b, R (a, x) :: ss)
  fun prune (a, b, _) = (a, b, nil)
  
  datatype 'a step = R of 'a tree * 'a | T
  
  fun rot ((a, x), (b, y)) = R (Tree (a,x,b), y)
  fun cut (us, vs) = foldl op:: us vs
  fun ins (R v :: R u :: T :: us, vs) = ins (us, rot (u, v) :: T :: vs)
    | ins (nil, vs) = cut (T :: nil, vs)
    | ins xs = cut xs
  
  fun upd (c, R (b,y) :: R (a,x) :: T :: ss) = upd (r3 (a,x,b,y,c), ss)
    | upd (b, R (a,x) :: T :: ss) = upd (Tree (a,x,b), ss)
    | upd (xs, _) = xs
  
  fun cons (x, ss) = ins (ss, R (Empty, x) :: nil)
  fun fromAsc xs = upd (Empty, foldl cons nil xs)
  
  datatype 'a step = L of 'a * 'a tree | T
  
  fun rot ((x, a), (y, b)) = L (x, Tree (a,y,b))
  fun cut (us, vs) = foldl op:: vs us
  fun ins (us, L u :: L v :: T :: vs) = ins (rot (u, v) :: T :: us, vs)
    | ins (us, nil) = cut (us, T :: nil)
    | ins xs = cut xs
  
  fun upd (a, L (x,b) :: L (y,c) :: T :: ss) = upd (l3 (a,x,b,y,c), ss)
    | upd (a, L (x,b) :: T :: ss) = upd (Tree (a,x,b), ss)
    | upd (xs, _) = xs
  
  fun cons (x, ss) = ins (L (x, Empty) :: nil, ss)
  fun fromDesc xs = upd (Empty, foldl cons nil xs)
  
  datatype 'a step = One of 'a | Many of 'a tree
  
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
