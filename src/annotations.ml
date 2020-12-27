open Variable

module VarAnnot = struct
  type t = (Env.t * Cduce.typ) list
  let empty = []
  let splits _ _ = failwith "TODO"
  let add_split _ _ _ = failwith "TODO"
end

module Annotations = struct
  type t = VarAnnot.t VarMap.t
  let empty = VarMap.empty
  let splits _ _ _ = failwith "TODO"
  let add_split _ _ _ _ = failwith "TODO"

  let mem_var _ _ = failwith "TODO"
  let add_var _ _ _ = failwith "TODO"
  let remove_var _ _ = failwith "TODO"
  let get_var _ _ = failwith "TODO"
end
