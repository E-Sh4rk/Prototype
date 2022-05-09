open Variable

val regroup : Variable.t -> (Env_refinement.t * 'a) list ->
    (Env_refinement.t * (Cduce.typ * 'a) list) list
