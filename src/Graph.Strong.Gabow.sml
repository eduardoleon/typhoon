structure GabowSCC :> STRONGLY_CONNECTED =
struct
  structure V = Vector
  structure A = IntArray
  
  datatype step
    = Visits of int list
    | Visit of int * int
    | Top of int
    | Collect of int * int list
  
  type graph = int list vector
  type state = int * int list * int list * step list
  type stream = graph * A.array * state ref
  
  fun sccs (graph, roots) =
    let
      val size = V.length graph
      val index = A.array (size, ~1)
      val state = ref (0, nil, nil, Visits roots :: nil)
    in
      (graph, index, state)
    end
  
  fun next (graph, index, state) =
    let
      val size = V.length graph
      
      fun run (n, is, js, Visits nil :: ss) = run (n, is, js, ss)
        | run (n, is, js, Visits (k :: ks) :: ss) =
          if k >= 0 andalso k < size then
            run (n, is, js, Visit (k, A.sub (index, k)) :: Visits ks :: ss)
          else
            run (n, is, js, Visits ks :: ss)
        
        (*  The index of a node k is the number of nodes that have been visited
         *  before the graph traversal reaches k.  We store the index of every
         *  node in the global array.
         *)
        | run (n, is, js, Visit (k, ~1) :: ss) =
          let in
            A.update (index, k, n);
            run (n + 1, k :: is, k :: js, Visits (V.sub (graph, k)) :: Top k :: ss)
          end
        
        (*  Discard nodes proven not to be SCC roots.  *)
        | run (n, is, nil, Visit _ :: ss) = run (n, is, nil, ss)
        | run (n, is, jjs as j :: js, Visit (k, c) :: ss) =
          if A.sub (index, j) > c then
            run (n, is, js, Visit (k, c) :: ss)
          else
            run (n, is, jjs, ss)
        
        (*  Collect a wholly visited SCC.  *)
        | run (n, is, jjs as j :: js, Top k :: ss) =
          if j = k then
            run (n, is, js, Collect (k, nil) :: ss)
          else
            run (n, is, jjs, ss)
        
        (*  Yield a wholly collected SCC.  *)
        | run (n, i :: is, js, Collect (k, ks) :: ss) =
          let in
            A.update (index, i, size);
            if i = k then
              k :: ks before state := (n, is, js, ss)
            else
              run (n, is, js, Collect (k, i :: ks) :: ss)
          end
        
        | run _ = nil
    in
      run (!state)
    end
end
