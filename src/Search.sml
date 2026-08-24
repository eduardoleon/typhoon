signature SEARCH_TREE =
sig
  type 'a tree
  type 'a leaf
  type 'a hole
  
  datatype 'a focus = Leaf of 'a leaf | Node of 'a * 'a hole
  
  val empty : 'a tree
  
  (* Navigation *)
  val root : 'a tree -> 'a focus
  val left : 'a * 'a hole -> 'a focus
  val right : 'a * 'a hole -> 'a focus
  
  (* Reconstruction *)
  val insert : 'a * 'a leaf -> 'a tree
  val update : 'a * 'a hole -> 'a tree
  val delete : 'a hole -> 'a tree
  val restore : 'a leaf -> 'a tree
  
  type 'a build_asc
  type 'a build_desc
  
  val fromAsc : unit -> 'a build_asc
  val fromDesc : unit -> 'a build_desc
  val putAsc : 'a build_asc * 'a -> unit
  val putDesc : 'a build_desc * 'a -> unit
  val buildAsc : 'a build_asc -> 'a tree
  val buildDesc : 'a build_desc -> 'a tree
  
  type 'a iter_asc
  type 'a iter_desc
  
  val toAsc : 'a tree -> 'a iter_asc
  val toDesc : 'a tree -> 'a iter_desc
  val nextAsc : 'a iter_asc -> 'a option
  val nextDesc : 'a iter_desc -> 'a option
end
