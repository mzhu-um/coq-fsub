# System F <: Benchmark

## Testing (Shifting/Lifting Substitution)

### Subtyping Transitivity 

$$
\dfrac{\Gamma \vdash S <: T \quad \Gamma \vdash T <: U}{\Gamma \vdash S <: U}
$$



### Subtyping Narrowing
$$
\dfrac{\Gamma, X <: Q \vdash M <: N \quad \Gamma \vdash P <: Q}{\Gamma, X <: P \vdash M <: N}
$$

### Subtyping Strengthening 

$$
\frac{\Gamma, x : Q \vdash S <: T}{\Gamma \vdash S <: T}
$$


##  Generate Typed Terms

### Generate (Concrete) Type Terms

- No terms has exactly type `Top` 
- Generate `Top` only as the supertype of the parameter in a type abstraction

### Generate Supertype

* Instead of generating terms of subtype, generate supertype based on subtype



## Testing

### Progress

```coq
typing empty t U -> value t \/ exists t', t --> t'
```

### Preservation

```coq
typing e t U -> red t t' -> typing e t' U
```







## Verification

### Reduction Semantics 

- `ctx_inj` can be wrong
- Not sure if it's correct
- Important to test progress
- POPLmark required
- Alternative: Plotkin smallstep / Parallel reduction
- Alternative: Test Both reduction strategy

### Type Checking

- Stuck! Subtyping correctness requires reasoning on fuel!
