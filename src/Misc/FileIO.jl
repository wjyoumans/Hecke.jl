
import Base: write
export save_ideal, read_facelem_ideal

function break_apart(I::NfOrdIdl)
  O = order(I)
  d = degree(O)
  K = nf(O)
  f = defining_polynomial(K)
  fcoeff = map(Rational{BigInt}, [coeff(f, i) for i in 0:degree(f)])
  M = basis_matrix(O)
  Obasismat = Rational{BigInt}[ M[i, j] for i in 1:d, j in 1:d]
  MI = basis_matrix(I)
  if Hecke.has_2_elem_normal(I)
    Idata = (true, BigInt(I.gen_one), _nf_elem_to_vector_bigint(I.gen_two.elem_in_nf))
  else
    Idata = (false, BigInt[ MI[i, j] for i in 1:d, j in 1:d])
  end

  A, mA = automorphism_group(K)
  auts = Vector{Rational{BigInt}}[_nf_elem_to_vector_bigint(Hecke.image_primitive_element(mA(a))) for a in A]
  return fcoeff, Obasismat, Idata, A.mult_table, auts
end

function assemble_ideal(fcoeff, Obasismat, Idata, mult_table, auts)
  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  f = Qx(map(fmpq, fcoeff))
  d = degree(f)
  K, a = NumberField(f, "a", cached = false)
  O = Order(K, matrix(FlintQQ, map(fmpq, Obasismat)), check = false)
  O.ismaximal = 1
  if Idata[1]
    I = ideal(O, fmpz(Idata[2]), O(K(Idata[3])))
    I.gens_normal = fmpz(Idata[2])
  else
    I = ideal(O, matrix(FlintZZ, map(fmpz, Idata[2])))
  end
  A = GrpGen(mult_table)
  autos = NfToNfMor[hom(K, K, K(b), check = false) for b in auts]
  Hecke.set_automorphisms(K, autos)
  Hecke._set_maximal_order(K, O)
  return I
end


function _nf_elem_to_vector_bigint(a::nf_elem)
  return Rational{BigInt}[Rational{BigInt}(coeff(a, i)) for i in 0:degree(parent(a)) - 1]
end

function break_apart(a::FacElem{nf_elem, AnticNumberField})
  z = Vector{Tuple{Vector{Rational{BigInt}}, BigInt}}()
  for (b, e) in a
    push!(z, (_nf_elem_to_vector_bigint(b), BigInt(e)))
  end
  return z
end

function assemble(K::AnticNumberField, z::Vector{Tuple{Vector{Rational{BigInt}}, BigInt}})
  res = Dict{nf_elem, fmpz}()
  for i in 1:length(z)
    res[K(z[i][1])] = fmpz(z[i][2])
  end
  return FacElem(res)
end

function assemble(K::AnticNumberField, z::Vector{Tuple{Vector{fmpq}, fmpz}})
  res = Dict{nf_elem, fmpz}()
  for i in 1:length(z)
    res[K(z[i][1])] = z[i][2]
  end
  return FacElem(res)
end

function break_apart(I::NfOrdIdl, mL::NfToNfMor)
  z = break_apart(I)
  L = domain(mL)
  return (z..., _nf_elem_to_vector_bigint(Hecke.image_primitive_element(mL)), break_apart(L)...)
end

function assemble_ideal_and_mor(fcoeff, Obasismat, Idata, mult_table, auts, prim_img, gcoeff, auts2)
  I = assemble_ideal(fcoeff, Obasismat, Idata, mult_table, auts)
  L = assemble_nf(gcoeff, auts2)
  mL = hom(L, nf(order(I)), nf(order(I))(prim_img))
  return I, mL
end

function break_apart(mL::NfToNfMor)
  L = domain(mL)
  return (_nf_elem_to_vector_bigint(Hecke.image_primitive_element(mL)), break_apart(L)...)
end

function assemble_mor(K, prim_img, gcoeff, auts2)
  L = assemble_nf(gcoeff, auts2)
  mL = hom(L, K, K(prim_img))
  return mL
end


function assemble(fcoeff, Obasismat, mult_table, auts)
  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  f = Qx(map(fmpq, fcoeff))
  d = degree(f)
  K, a = NumberField(f, "a", cached = false)
  O = Order(K, matrix(FlintQQ, map(fmpq, Obasismat)))
  A = GrpGen(mult_table)
  autos = NfToNfMor[hom(K, K, K(b), check = false) for b in auts]
  O.ismaximal = 1
  Hecke.set_automorphisms(K, autos)
  Hecke._set_maximal_order(K, O)
  return K, O
end

function break_apart(K::AnticNumberField)
  f = defining_polynomial(K)
  fcoeff = map(Rational{BigInt}, [coeff(f, i) for i in 0:degree(f)])
  A, mA = automorphism_group(K)
  auts = Vector{Vector{Rational{BigInt}}}()
  for a in A
    push!(auts, _nf_elem_to_vector_bigint(Hecke.image_primitive_element(mA(a))))
  end
  return fcoeff, auts
end

function assemble_nf(fcoeff, auts)
  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  f = Qx(map(fmpq, fcoeff))
  d = degree(f)
  K, a = NumberField(f, "a", cached = false)
  autos = NfToNfMor[hom(K, K, K(b), check = false) for b in auts]
  Hecke.set_automorphisms(K, autos)
  return K
end



################################################################################
#
#  Number field elements
#
################################################################################

function save_element(a::nf_elem, file::String)
  open(file, "w") do f
    write(f, string(_nf_elem_to_vector_bigint(a)))
    write(f, "\n")
  end
end

function save_elements(A, file::String)
  open(file, "w") do f
    for a in A
      write(f, string(_nf_elem_to_vector_bigint(a)))
      write(f, "\n")
    end
  end
end

function read_element(K::AnticNumberField, file::String)
  local el
  open(file, "r") do f
    for s in eachline(f)
      s = replace(s, "\"" => "")
      data = Meta.eval(Meta.parse(s))
      el = K(data)
    end
  end
  return el
end

function read_elements(K::AnticNumberField, file::String)
  elts=[]
  open(file, "r") do f
    for s in eachline(f)
      s = replace(s, "\"" => "")
      data = Meta.eval(Meta.parse(s))
      push!(elts, K(data))
    end
  end
  return elts
end


################################################################################
#
#  Factored elements
#
################################################################################

function save_factored_element(a::FacElem{nf_elem, AnticNumberField}, file::String)
  open(file, "w") do f
    write(f, string(break_apart(a)))
    write(f, "\n")
  end
end

function save_factored_elements(A, file::String)
  open(file, "w") do f
    for a in A
      write(f, string(break_apart(a)))
      write(f, "\n")
    end
  end
end

function read_factored_element(K::AnticNumberField, file::String)
  local el
  open(file, "r") do f
    for s in eachline(f)
      data = Meta.eval(Meta.parse(s))
      el = assemble(K, data)
    end
  end
  return el
end

function read_factored_element_2(K::AnticNumberField, file::String)
  local el
  open(file, "r") do f
    skip(f, 39) # this is the head of Tuple{....}[..]
                # start at [...]
    _, data = Hecke._parse(Vector{Tuple{Vector{fmpq}, fmpz}}, f)
    el = assemble(K, data)
  end
  return el
end

function read_factored_elements(K::AnticNumberField, file::String)
  elts=FacElem[]
  open(file, "r") do f
    for s in eachline(f)
      data = Meta.eval(Meta.parse(s))
      push!(elts, assemble(K, data))
    end
  end
  return elts
end

################################################################################
#
#  ideals
#
################################################################################

function save_ideal(I::NfOrdIdl, file::String)
  K = nf(I)
  Hecke.assure_2_normal(I)
  save_elements([K(I.gen_one), K(I.gen_two)], file)
end

function save_ideal(I::FacElem{NfOrdIdl}, file::String)
  d = Dict(I)
  ks = keys(d)
  K = nf(first(ks))

  open(file, "w") do f
    for k in ks
      Hecke.assure_2_normal(k)
      A = [K(k.gen_one), K(k.gen_two)]
      for a in A
	write(f, string(_nf_elem_to_vector_bigint(a)))
	write(f, "\n")
      end
      write(f, "$(d[k])\n")
    end
  end
end

function read_facelem_ideal(OK::NfOrd, file::String)
  K = nf(OK)
  
  out = Dict{NfOrdIdl, Int}()
  elts=[]
  open(file, "r") do f
    for (i, s) in enumerate(eachline(f))
      @show i

      if i % 3 == 0
	@assert length(elts) == 2
	e = Meta.parse(s)
	I = ideal(OK, ZZ(elts[1]), OK(elts[2]))
	out[I] = e
	elts=[]
	continue
      end

      s = replace(s, "\"" => "")
      data = Meta.eval(Meta.parse(s))
      push!(elts, K(data))
    end
  end
  return FacElem(out)
end

function read_ideal(OK::NfOrd, file::String)
  K = nf(OK)
  gens = read_elements(K, file)
  I = ideal(OK, ZZ(gens[1]), OK(gens[2]))
  return I
end

function save_ideals(V::Vector{NfOrdIdl}, file::String)
  K = nf(V[1])
  gens = []
  for I in V
    Hecke.assure_2_normal(I)
    push!(gens, K(I.gen_one))
    push!(gens, K(I.gen_two))
  end
  save_elements(gens, file)
end

function read_ideals(OK::NfOrd, file::String)
  K = nf(OK)

  V = []
  gens = read_elements(K, file)
  for i = 1:length(gens)
    if i % 2 == 1
      push!(V, ideal(OK, ZZ(gens[i]), OK(gens[i+1])))
    end
  end
  return V
end
