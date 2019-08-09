
module List = struct 
  include Base.List 
  let rec foldk ~f ~(init: 'acc) ~finish = function
    | [] -> finish init 
    | x::xs -> f init x xs (fun init -> foldk ~f ~finish ~init xs)

end 