# pure

This folder contains an implementation of a "pure" lambda calculus but with normal-order reduction. The changes are very, very minimal:

```diff
77c77
< evalApp2 (App t1 t2) = do
---
> evalApp2 (App v1 t2) | isValue v1 = do
79c79
<   return $ App t1 t2'
---
>   return $ App v1 t2'
```