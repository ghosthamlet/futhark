-- Example program from the ARRAY'14 paper.
-- ==

let main [m][n] (xs: *[]i32, as: *[m][n]f64): [][]f64 =
  map  (\(e: (i32, *[]f64)): *[]f64  ->
         unsafe
         let (i, a) = e in
         let a = loop(a) for j < n do
           let a[j] = a[ xs[j] ] * 2.0 in a
         in
         map  (\(j: i32): f64  ->
                if (j < 2*i) && (xs[j] == j)
                then a[j*i] else 0.0
             ) (iota(n))
      ) (zip (iota(m)) as )
