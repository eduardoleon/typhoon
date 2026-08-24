signature SET =
sig
  type key
  type set
  type rest
  
  val empty : set
  val get : key * set -> bool * rest
  val set : bool * rest -> set
  
  type iter_asc
  type iter_desc
  
  val toAsc : set -> iter_asc
  val toDesc : set -> iter_desc
  val nextAsc : iter_asc -> key option
  val nextDesc : iter_desc -> key option
end

signature MAP =
sig
  type key
  type 'a elem = key * 'a
  type 'a map
  type 'a rest
  
  val empty : 'a map
  val get : key * 'a map -> 'a option * 'a rest
  val set : 'a option * 'a rest -> 'a map
  
  type 'a iter_asc
  type 'a iter_desc
  
  val toAsc : 'a map -> 'a iter_asc
  val toDesc : 'a map -> 'a iter_desc
  val nextAsc : 'a iter_asc -> 'a elem option
  val nextDesc : 'a iter_desc -> 'a elem option
end
