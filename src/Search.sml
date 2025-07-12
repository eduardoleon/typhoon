signature SEARCH_TREE =
sig
  type 'a tree
  type 'a leaf
  type 'a hole
  
  datatype 'a focus = Leaf of 'a leaf | Node of 'a * 'a hole
  
  val empty : 'a tree
  
  val root : 'a tree -> 'a focus
  val left : 'a * 'a hole -> 'a focus
  val right : 'a * 'a hole -> 'a focus
  
  val insert : 'a * 'a leaf -> 'a tree
  val update : 'a * 'a hole -> 'a tree
  val delete : 'a hole -> 'a tree
  val splay : 'a leaf -> 'a tree
  val prune : 'a hole -> 'a hole
  
  val fromAsc : 'a list -> 'a tree
  val fromDesc : 'a list -> 'a tree
  
  val toAsc : 'a tree -> 'a list
  val toDesc : 'a tree -> 'a list
end
