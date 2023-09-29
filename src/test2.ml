let (<=) = <Int -> Int -> Bool>
let (>=) = <Int -> Int -> Bool>
let (<) = <Int -> Int -> Bool>
let (>) = <Int -> Int -> Bool>
let (=) = <Any -> Any -> Bool>

type Key = Int

type T 'a =
  Nil | (T 'a, Key, 'a, T 'a, Int)

let height x =
  match x with
  | :Nil -> 0
  | (_,_,_,_,h) -> h
  end
let height : T 'a -> Int = height

let create l x d r =
  let hl = height l in
  let hr = height r in
  (l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))

let singleton x d = (nil, x, d, nil, 1)

let bal (l:T 'a) (x: Key) (d:'a) (r:T 'a) =
  let hl = match l with :Nil -> 0 | (_,_,_,_,h) -> h end in
  let hr = match r with :Nil -> 0 | (_,_,_,_,h) -> h end in
  if hl > (hr + 2) then
    match l with
      :Nil -> <Empty>
    | (ll, lv, ld, lr, _) ->
        if (height ll) >= (height lr) then
          create ll lv ld (create lr x d r)
        else
          match lr with
            :Nil -> <Empty>
          | (lrl, lrv, lrd, lrr, _)->
              create (create ll lv ld lrl) lrv lrd (create lrr x d r)
        end
  end else if hr > (hl + 2) then
    match r with
      :Nil -> <Empty>
    | (rl, rv, rd, rr, _) ->
        if (height rr) >= (height rl) then
          create (create l x d rl) rv rd rr
        else
          match rl with
            :Nil -> <Empty>
          | (rll, rlv, rld, rlr, _) ->
              create (create l x d rll) rlv rld (create rlr rv rd rr)
        end
  end else
    (l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))

let bal : T 'a -> Key -> 'a -> T 'a -> T 'a = bal