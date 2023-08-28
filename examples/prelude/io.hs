main :: IO ()
main = Ret ()

return v = Ret v

bind x f = Bind x f

app :: (a -> IO b) -> [a] -> IO ()
app f l = case l of [] -> return ()
                    h:t -> do f h ; app f t

read_args n =
  let make_str n = if n < 1 then ""
                   else #(__Concat) " " (make_str (n - 1))
  in Act (#(cline_arg) (make_str n))

print :: String -> IO String
print s = Act (#(stdout) s)

println :: String -> IO String
println s = print (#(__Concat) s "\n")

