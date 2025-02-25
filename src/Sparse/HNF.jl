################################################################################
#
#  Reduction of sparse rows modulo sparse upper triangular matrices
#
################################################################################

@doc Markdown.doc"""
    reduce(A::SMat{T}, g::SRow{T}) -> SRow{T}

Given an upper triangular matrix $A$ over a field and a sparse row $g$, this
function reduces $g$ modulo $A$.
"""
function reduce(A::SMat{T}, g::SRow{T}) where {T <: FieldElement}
  return _reduce_field(A, g)
end

function reduce(A::SMat{zzModRingElem}, g::SRow{zzModRingElem})
  return _reduce_field(A, g)
end

function _reduce_field(A::SMat{T}, g::SRow{T}) where {T}
  @hassert :HNF 1  isupper_triangular(A)
  #assumes A is upper triangular, reduces g modulo A
  # supposed to be a field...
  if A.r == A.c
    return sparse_row(base_ring(A))
  end
  while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= nrows(A) && A.rows[j].pos[1] < s
      j += 1
    end
    if j > nrows(A) || A.rows[j].pos[1] > s
      break
    end
    @hassert :HNF 2  A.rows[j].pos[1] == g.pos[1]
    @hassert :HNF 2  (A.rows[j].values[1]) == 1
    p = g.values[1]
    g = Hecke.add_scaled_row(A[j], g, -p)
    @hassert :HNF 2  length(g)==0 || g.pos[1] > A[j].pos[1]
  end
  if length(g) > 0
    li = inv(g.values[1])
    for i=1:length(g)
      g.values[i] *= li
    end
  end
  return g
end

@doc Markdown.doc"""
    reduce(A::SMat{ZZRingElem}, g::SRow{ZZRingElem}) -> SRow{ZZRingElem}

Given an upper triangular matrix $A$ over a field and a sparse row $g$, this
function reduces $g$ modulo $A$.
"""
function reduce(A::SMat{T}, g::SRow{T}) where {T}
  @hassert :HNF 1  isupper_triangular(A)
  #assumes A is upper triangular, reduces g modulo A
  #until the 1st (pivot) change in A
  new_g = false
  while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= nrows(A) && A.rows[j].pos[1] < s
      j += 1
    end
    if j > nrows(A) || A.rows[j].pos[1] > s
      if g.values[1] < 0
        if !new_g
          g = copy(g)
        end
        for i=1:length(g.values)
          g.values[i] *= -1
        end
      end
      return g
    end
    p = g.values[1]
    if divides(p, A.rows[j].values[1])[1]
      g = Hecke.add_scaled_row(A[j], g, - divexact(p, A.rows[j].values[1]))
      new_g = true
      @hassert :HNF 2  length(g)==0 || g.pos[1] > A[j].pos[1]
    else
      x, a, b = gcdx(A.rows[j].values[1], p)
      @hassert :HNF 2  x > 0
      c = -div(p, x)
      d = div(A.rows[j].values[1], x)
      A[j], g = Hecke.transform_row(A[j], g, a, b, c, d)
      new_g = true
      @hassert :HNF 2  A[j].values[1] == x
      @hassert :HNF 2  length(g)==0 || g.pos[1] > A[j].pos[1]
    end
  end

  if length(g.values) > 0 && g.values[1] < 0
    if !new_g
      g = copy(g)
    end
    for i=1:length(g.values)
      g.values[i] *= -1
    end
  end
  return g
end

@doc Markdown.doc"""
    reduce(A::SMat{ZZRingElem}, g::SRow{ZZRingElem}, m::ZZRingElem) -> SRow{ZZRingElem}

Given an upper triangular matrix $A$ over the integers, a sparse row $g$ and an
integer $m$, this function reduces $g$ modulo $A$ and returns $g$
modulo $m$ with respect to the symmetric residue system.
"""
function reduce(A::SMat{T}, g::SRow{T}, m::T) where {T}
  @hassert :HNF 1  isupper_triangular(A)
  #assumes A is upper triangular, reduces g modulo A
  g = copy(g)
  mod_sym!(g, m)
  while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= nrows(A) && A.rows[j].pos[1] < s
      j += 1
    end
    if j > nrows(A) || A.rows[j].pos[1] > s
      if mod_sym(g.values[1], m) < 0
        for i=1:length(g.values)
          g.values[i] *= -1
        end
        @hassert :HNF 3  mod_sym(g.values[1], m) > 0
      end
      mod_sym!(g, m)
      return g
    end
    st_g = 2
    st_A = 2
    p = g.values[1]
    if divides(p, A.rows[j].values[1])[1]
      g = add_scaled_row(A[j], g, - divexact(p, A.rows[j].values[1]))
      mod_sym!(g, m)
      @hassert :HNF 2  length(g)==0 || g.pos[1] > A[j].pos[1]
    else
      x, a, b = gcdx(A.rows[j].values[1], p)
      @hassert :HNF 2  x > 0
      c = -div(p, x)
      d = div(A.rows[j].values[1], x)
      A[j], g = Hecke.transform_row(A[j], g, a, b, c, d)
      new_g = true
#      @hassert :HNF 2  A[j].values[1] == x
      mod_sym!(g, m)
      mod_sym!(A[j], m)
#      @hassert :HNF 2  length(g)==0 || g.pos[1] > A[j].pos[1]
#      @hassert :HNF 2  A[j].values[1] > 0
    end
  end
  if length(g.values) > 0 && mod_sym(g.values[1], m) < 0
    for i=1:length(g.values)
      g.values[i] *= -1
    end
  end
  Hecke.mod_sym!(g, m)
#  @hassert :HNF 1  length(g.pos) == 0 || g.values[1] >= 0
  return g
end

function mod_sym(a::T, b::T) where {T}
  return mod(a, b)
end
function mod_sym!(a::T, b::T) where {T}
  return mod!(a, b)
end

function mod_sym!(a::ZZRingElem, b::ZZRingElem)
  mod!(a, a, b)
  if a>div(b, 2)
    sub!(a, a, b)
  end
  return a
end

################################################################################
#
#  Saturation
#
################################################################################

@doc Markdown.doc"""
    saturate(A::SMat{ZZRingElem}) -> SMat{ZZRingElem}

Computes the saturation of $A$, that is, a basis for $\mathbf{Q}\otimes M \meet
\mathbf{Z}^n$, where $M$ is the row span of $A$ and $n$ the number of rows of
$A$.

Equivalently, return $TA$ for an invertible rational matrix $T$, such that $TA$
is integral and the elementary divisors of $TA$ are all trivial.
"""
function saturate(A::SMat{ZZRingElem})
  Hti = transpose(hnf(transpose(A)))
  Hti = sub(Hti , 1:nrows(Hti), 1:nrows(Hti))
  Hti = transpose(Hti)
  S, s = solve_ut(Hti, transpose(A))
  @assert isone(s)
  SS = transpose(S)
  return SS
end

################################################################################
#
#  Hermite normal form using Kannan-Bachem algorithm
#
################################################################################

@doc Markdown.doc"""
    find_row_starting_with(A::SMat, p::Int) -> Int

Tries to find the index $i$ such that $A_{i,p} \neq 0$ and $A_{i, p-j} = 0$
for all $j > 1$. It is assumed that $A$ is upper triangular.
If such an index does not exist, find the smallest index larger.
"""
function find_row_starting_with(A::SMat, p::Int)
#  @hassert :HNF 1  isupper_triangular(A)
  start = 0
  stop = nrows(A)+1
  while start < stop - 1
    mid = div((stop + start), 2)
    if A[mid].pos[1] == p
      return mid
    elseif A[mid].pos[1] < p
      start = mid
    else
      stop = mid
    end
  end
  return stop
end

# If trafo is set to Val{true}, then additionaly an Array of transformations
# is returned.
function reduce_up(A::SMat{T}, piv::Vector{Int},
                                  trafo::Type{Val{N}} = Val{false}) where {N, T}

  with_transform = (trafo == Val{true})
  if with_transform
    trafos = SparseTrafoElem{T, dense_matrix_type(T)}[]
  end

  sort!(piv)
  p = find_row_starting_with(A, piv[end])

  for red=p-1:-1:1
    # the last argument should be the smallest pivot larger then pos[1]
    if with_transform
      A[red], new_trafos = reduce_right(A, A[red], max(A[red].pos[1]+1, piv[1]), trafo)
      for t in new_trafos
        t.j = red
      end
      append!(trafos, new_trafos)
    else
      A[red] = reduce_right(A, A[red], max(A[red].pos[1]+1, piv[1]))
    end
  end
  with_transform ? (return trafos) : nothing
end

# If trafo is set to Val{true}, then additionaly an Array of transformations
# is returned.
@doc Markdown.doc"""
    reduce_full(A::SMat{ZZRingElem}, g::SRow{ZZRingElem},
                          trafo = Val{false}) -> SRow{ZZRingElem}, Vector{Int}

Reduces $g$ modulo $A$ and assumes that $A$ is upper triangular.

The second return value is the array of pivot elements of $A$ that changed.

If `trafo` is set to `Val{true}`, then additionally an array of transformations
is returned.
"""
function reduce_full(A::SMat{T}, g::SRow{T}, trafo::Type{Val{N}} = Val{false}) where {N, T}
#  @hassert :HNF 1  isupper_triangular(A)
  #assumes A is upper triangular, reduces g modulo A

  with_transform = (trafo == Val{true})
  no_trafo = (trafo == Val{false})

  if with_transform
    trafos = SparseTrafoElem{T, dense_matrix_type(T)}[]
  end

  new_g = false

  piv = Int[]
  while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= nrows(A) && A.rows[j].pos[1] < s
      j += 1
    end
    if j > nrows(A) || A.rows[j].pos[1] > s
      if !isone(canonical_unit(g.values[1]))
        # Multiply row g by -1
        if with_transform
          push!(trafos, sparse_trafo_scale(nrows(A) + 1, base_ring(A)(inv(canonical_unit(g.values[1])))))
        end
        if !new_g
          g = copy(g)
        end
        for i=1:length(g.values)
          g.values[i] *= -1
        end
      end

      if with_transform
        g, new_trafos  = reduce_right(A, g, 1, trafo)
        append!(trafos, new_trafos)
      else
        g = reduce_right(A, g)
      end
      new_g = true

      if A.r == A.c
        @hassert :HNF 1  length(g) == 0 || minimum(g) >= 0
      end

      with_transform ? (return g, piv, trafos) : (return g, piv)

    end
    p = g.values[1]
    if divides(p, A.rows[j].values[1])[1]
      sca =  -divexact(p, A.rows[j].values[1])
      g = Hecke.add_scaled_row(A[j], g, sca)
      new_g = true
      with_transform ? push!(trafos, sparse_trafo_add_scaled(j, nrows(A) + 1, sca)) : nothing
      @hassert :HNF 1  length(g)==0 || g.pos[1] > A[j].pos[1]
    else
      x, a, b = gcdx(A.rows[j].values[1], p)
      @hassert :HNF 1  x > 0
      c = -div(p, x)
      d = div(A.rows[j].values[1], x)
      A[j], g = Hecke.transform_row(A[j], g, a, b, c, d)
      new_g = true
      if with_transform
        push!(trafos, sparse_trafo_para_add_scaled(j, nrows(A) + 1, a, b, c, d))
      end
      @hassert :HNF 1  A[j].values[1] == x
      @hassert :HNF 1  length(g)==0 || g.pos[1] > A[j].pos[1]
      push!(piv, A[j].pos[1])
      if with_transform
        A[j], new_trafos = reduce_right(A, A[j], A[j].pos[1]+1, trafo)
        # We are updating the jth row
        # Have to adjust the transformations
        for t in new_trafos
          t.j = j
        end
        # Now append
        append!(trafos, new_trafos)
      else
        A[j] = reduce_right(A, A[j], A[j].pos[1]+1, trafo)
      end

      if A.r == A.c
        @hassert :HNF 1  minimum(A[j]) >= 0
      end
    end
  end
  if length(g.values) > 0 && g.values[1] < 0
    if !new_g
      g = copy(g)
    end
    for i=1:length(g.values)
      g.values[i] *= -1
    end
    with_transform ? push!(trafos, sparse_trafo_scale!{ZZRingElem}(nrows(A) + 1, ZZRingElem(-1))) : nothing
  end
  if with_transform
    g, new_trafos = reduce_right(A, g, 1, trafo)
    append!(trafos, new_trafos)
  else
    g = reduce_right(A, g)
  end
  if A.r == A.c
    @hassert :HNF 1  length(g) == 0 || minimum(g) >= 0
  end
  with_transform ? (return g, piv, trafos) : (return g, piv)
end

function reduce_right(A::SMat{T}, b::SRow{T},
                      start::Int = 1, trafo::Type{Val{N}} = Val{false}) where {N, T}
  with_transform = (trafo == Val{true})
  with_transform ? trafos = [] : nothing
  new = true
  if length(b.pos) == 0
    with_transform ? (return b, trafos) : return b
  end
  j = 1
  while j <= length(b.pos) && b.pos[j] < start
    j += 1
  end
  if j > length(b.pos)
    with_transform ? (return b, trafos) : return b
  end
  p = find_row_starting_with(A, b.pos[j])
  if p > nrows(A)
    with_transform ? (return b, trafos) : return b
  end
  @hassert :HNF 1  A[p] != b
  while j <= length(b.pos)
    while p<nrows(A) && A[p].pos[1] < b.pos[j]
      p += 1
    end
    if A[p].pos[1] == b.pos[j]
      q, r = divrem(b.values[j], A[p].values[1])
      if T == ZZRingElem && r < 0
        q -= 1
        r += A[p].values[1]
        @hassert :HNF 1  r >= 0
      end
      if q != 0
        if new
          b = Hecke.add_scaled_row(A[p], b, -q)
          new = false
        else
          Hecke.add_scaled_row!(A[p], b, -q)
        end

        with_transform ? push!(trafos, sparse_trafo_add_scaled(p, nrows(A) + 1, -q)) : nothing
        if r == 0
          j -= 1
        else
          @hassert :HNF 1  b.values[j] == r
        end
      end
    end
    j += 1
  end
  with_transform ? (return b, trafos) : return b
end

@doc Markdown.doc"""
    hnf_extend!(A::SMat{ZZRingElem}, b::SMat{ZZRingElem}, offset::Int = 0) -> SMat{ZZRingElem}

Given a matrix $A$ in HNF, extend this to get the HNF of the concatenation
with $b$.
"""
function hnf_extend!(A::SMat{T}, b::SMat{T}, trafo::Type{Val{N}} = Val{false}; truncate::Bool = false, offset::Int = 0) where {N, T}
  rA = nrows(A)
  @vprint :HNF 1 "Extending HNF by:\n"
  @vprint :HNF 1 b
  @vprint :HNF 1 "density $(density(A)) $(density(b))"

  with_transform = (trafo == Val{true})
  with_transform ? trafos = SparseTrafoElem{T, dense_matrix_type(T)}[] : nothing

  A_start_rows = nrows(A)  # for the offset stuff

  nc = 0
  for i=b
    if with_transform
      q, w, new_trafos = reduce_full(A, i, trafo)
      append!(trafos, new_trafos)
    else
      q, w = reduce_full(A, i)
    end

    if length(q) > 0
      p = find_row_starting_with(A, q.pos[1])
      if p > length(A.rows)
        # Appending row q to A
        # Do not need to track a transformation
        push!(A, q)
      else
        # Inserting row q at position p
        insert!(A.rows, p, q)
        A.r += 1
        A.nnz += length(q)
        A.c = max(A.c, q.pos[end])
        # The transformation is swapping pairwise from nrows(B) to p.
        # This should be the permutation matrix corresponding to
        # (k k-1)(k-1 k-2) ...(p+1 p) where k = nrows(B)
        if with_transform
          for j in nrows(A):-1:(p+1)
            push!(trafos, sparse_trafo_swap(T, j, j - 1))
          end
        end
      end
      push!(w, q.pos[1])
    else
      # Row i was reduced to zero
      with_transform ? push!(trafos, sparse_trafo_move_row(T, nrows(A) + 1, rA + nrows(b))) : nothing
    end
    if length(w) > 0
      if with_transform
        new_trafos = reduce_up(A, w, trafo)
        append!(trafos, new_trafos)
      else
        reduce_up(A, w)
      end
    end
    @v_do :HNF 1 begin
      if nc % 10 == 0
        println("Now at $nc rows of $(nrows(b)), HNF so far $(nrows(A)) rows")
        println("Current density: $(density(A))")
        println("and size of largest entry: $(nbits(maximum(abs, A))) bits $(sum(nbits, A))")
      end
    end
    nc += 1
  end
  if !truncate
    for i in 1:nrows(b)
      push!(A, sparse_row(base_ring(A)))
    end
  end

  if with_transform && offset != 0
    change_indices!(trafos, A_start_rows, offset)
  end

  with_transform ? (return A, trafos) : (return A)
end

function nbits(s::SRow{ZZRingElem})
  return sum(nbits, s.values)
end

@doc Markdown.doc"""
    hnf_kannan_bachem(A::SMat{ZZRingElem}) -> SMat{ZZRingElem}

Compute the Hermite normal form of $A$ using the Kannan-Bachem algorithm.
"""
function hnf_kannan_bachem(A::SMat{T}, trafo::Type{Val{N}} = Val{false}; truncate::Bool = false) where {N, T}
  @vprint :HNF 1 "Starting Kannan Bachem HNF on:\n"
  @vprint :HNF 1 A
  @vprint :HNF 1 "with density $(density(A)); truncating $truncate"

  with_transform = (trafo == Val{true})
  with_transform ? trafos = SparseTrafoElem{T, dense_matrix_type(T)}[] : nothing

  B = sparse_matrix(base_ring(A))
  B.c = A.c
  nc = 0
  for i=A
    if with_transform
      q, w, new_trafos = reduce_full(B, i, trafo)
      append!(trafos, new_trafos)
    else
      q, w = reduce_full(B, i)
    end

    if length(q) > 0
      p = find_row_starting_with(B, q.pos[1])
      if p > length(B.rows)
        # Appending row q to B
        # Do not need to track a transformation
        push!(B, q)
      else
        # Inserting row q at position p
        insert!(B.rows, p, q)
        B.r += 1
        B.nnz += length(q)
        B.c = max(B.c, q.pos[end])
        # The transformation is swapping pairwise from nrows(B) to p.
        # This should be the permutation matrix corresponding to
        # (k k-1)(k-1 k-2) ...(p+1 p) where k = nrows(B)
        if with_transform
          for j in nrows(B):-1:(p+1)
            push!(trafos, sparse_trafo_swap(T, j, j - 1))
          end
        end
      end
      push!(w, q.pos[1])
    else
      # Row i was reduced to zero
      with_transform ? push!(trafos, sparse_trafo_move_row(T, nrows(B) + 1, nrows(A))) : nothing
    end
    if length(w) > 0
      if with_transform
        new_trafos = reduce_up(B, w, trafo)
        append!(trafos, new_trafos)
      else
        reduce_up(B, w)
      end
    end
    @v_do :HNF 1 begin
      if nc % 10 == 0
        println("Now at $nc rows of $(nrows(A)), HNF so far $(nrows(B)) rows")
        println("Current density: $(density(B))")
        println("and size of largest entry: $(nbits(maximum(abs, B))) bits")
      end
    end
    nc += 1
  end
  if !truncate
    for i in 1:(nrows(A) - nrows(B))
      push!(B, sparse_row(base_ring(A)))
    end
  end
  with_transform ? (return B, trafos) : (return B)
end

@doc Markdown.doc"""
    hnf(A::SMat{ZZRingElem}) -> SMat{ZZRingElem}

Return the upper right Hermite normal form of $A$.
"""
function hnf(A::SMat{ZZRingElem}; truncate::Bool = false)
  return hnf_kannan_bachem(A, truncate = truncate)
end

@doc Markdown.doc"""
    hnf!(A::SMat{ZZRingElem})

Inplace transform of $A$ into upper right Hermite normal form.
"""
function hnf!(A::SMat{ZZRingElem}; truncate::Bool = false)
  B = hnf(A, truncate = truncate)
  A.rows = B.rows
  A.nnz = B.nnz
  A.r = B.r
  A.c = B.c
end



function reduce_right!(A::SMat{ZZRingElem}, b::SRow{ZZRingElem})
  if length(b.pos) == 0
    return b
  end
  j = 1
  p = find_row_starting_with(A, b.pos[j])
  if p > nrows(A)
    return b
  end
  while j <= length(b.pos)
    while p < nrows(A) && A[p].pos[1] < b.pos[j]
      p += 1
    end
    if A[p].pos[1] == b.pos[j]
      q, r = divrem(b.values[j], A[p].values[1])
      if r < 0
        q -= 1
        r += A[p].values[1]
        @hassert :HNF 1 r >= 0
      end
      if q != 0
        Hecke.add_scaled_row!(A[p], b, -q)
        if r == 0
          j -= 1
        else
          @hassert :HNF 1 b.values[j] == r
        end
      end
    end
    j += 1
  end
  return b
end
