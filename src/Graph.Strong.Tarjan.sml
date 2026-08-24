structure TarjanSCC :> STRONGLY_CONNECTED =
struct
  structure V = Vector
  structure A = IntArray
  
  datatype step
    = Roots of int list
    | Visit of int * int
    | Children of int * int * int list
    | Bump of int * int * int * int list
    | Collect of int * int list
  
  type graph = int list vector
  type state = int * int list * step list
  type stream = graph * A.array * state ref
  
  fun sccs (graph, roots) =
    let
      val size = V.length graph
      val index = A.array (size, ~1)
      val state = ref (0, nil, Roots roots :: nil)
    in
      (graph, index, state)
    end
  
  fun next (graph, index, state) =
    let
      val size = V.length graph
      
      fun run (n, is, Roots (j :: js) :: ss) =
          if j >= 0 andalso j < size then
            run (n, is, Visit (j, A.sub (index, j)) :: Roots js :: ss)
          else
            run (n, is, Roots js :: ss)
        
        (*  The lowlink of j is the earliest visited node that is reachable
         *  from j following a path with at most one backlink.
         *  
         *  If j is in the step stack, we store j's index.  Otherwise, we
         *  store the index of j's lowlink.
         *)
        | run (n, is, Visit (j, ~1) :: ss) =
          let in
            A.update (index, j, n);
            run (n + 1, j :: is, Children (j, n, V.sub (graph, j)) :: ss)
          end
        
        | run (n, is, Visit _ :: ss) = run (n, is, ss)
        
        (*  Visiting a child is different from visiting a root...  *)
        | run (n, is, Children (j, c, k :: ks) :: ss) =
          if k >= 0 andalso k < size then
            run (n, is, Visit (k, A.sub (index, k)) :: Bump (j, c, k, ks) :: ss)
          else
            run (n, is, Children (j, c, ks) :: ss)
        
        (*  ... because we must update the parent's lowlink estimate.  *)
        | run (n, is, Bump (j, c, k, ks) :: ss) =
          run (n, is, Children (j, Int.min (c, A.sub (index, k)), ks) :: ss)
        
        (*  Collect a wholly visited SCC.  *)
        | run (n, is, Children (j, c, nil) :: ss) =
          if A.sub (index, j) = c then
            run (n, is, Collect (j, nil) :: ss)
          else
            (A.update (index, j, c); run (n, is, ss))
        
        (*  Yield a wholly collected SCC.  *)
        | run (n, i :: is, Collect (j, js) :: ss) =
          let in
            A.update (index, i, size);
            if i = j then
              j :: js before state := (n, is, ss)
            else
              run (n, is, Collect (j, i :: js) :: ss)
          end
        
        | run _ = nil
    in
      run (!state)
    end
end
