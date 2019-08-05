let rec fib1 n = 
  if n <=1 then 1
  else if n <= 2 then 1
  else (fib1 (n-1)) + (fib1 (n-2))