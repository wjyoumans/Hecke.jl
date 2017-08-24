
export iscoprime, ray_class_group, isabelian, norm_group



#
# Test if two ideals $I,J$ in a maximal order are coprime.
#
doc"""
***
    iscoprime(I::NfOrdIdl, J::NfOrdIdl) -> Bool
> Test if ideals $I,J$ are coprime

"""

function iscoprime(I::NfOrdIdl, J::NfOrdIdl)
  
  @assert parent(I)==parent(J)
  
  if gcd(minimum(I), minimum(J))==1
    return true
  else 
    return isone(I+J)
  end

end 

#
# Modify the map of the class group so that the chosen representatives are coprime to m
# 

function _coprime_ideal(C::GrpAbFinGen, mC::Map, m::NfOrdIdl)
 
  O=parent(m).order
  K=nf(O)
  L=NfOrdIdl[]
  for i=1:ngens(C)
    a=mC(C[i])
    if iscoprime(a,m)
      push!(L,a)
    else  
      J=inv(a)
      s=K(rand(J.num,5))//J.den  # Is the bound acceptable?
      I=s*a
      simplify(I)
      I = num(I)
      while !iscoprime(I,m)
        s=K(rand(J.num,5))//J.den  
        I=s*a
        simplify(I)
        I = num(I)
      end
      push!(L,I)
    end
  end
  
  function exp(a::GrpAbFinGenElem)
    I=ideal(O,1)
    for i=1:ngens(C)
      if Int(a.coeff[1,i])!= 0
        I=I*(L[i]^(Int(a.coeff[1,i])))
      end
    end
    return I
  end
  
  mp=Hecke.MapClassGrp{typeof(C)}()
  mp.header=Hecke.MapHeader(C,Hecke.NfOrdIdlSet(O),exp, mC.header.preimage)
  
  return mp
 
end 

#
# Function that finds the generators of the infinite part
#

function _infinite_primes(O::NfOrd, p::Array{InfPlc,1}, m::NfOrdIdl)

  K=O.nf
  S=DiagonalGroup([2 for i=1:length(p)])

  function logS(x::Array{Int, 1})
    return S([x[i] > 0 ? 0 : 1 for i=1:length(x)])
  end

  s = typeof(S[1])[]
  g = elem_type(O)[]
  u, mu = sub(S, s)
  b = 10
  cnt = 0
  while true
    a = rand(m, b)
    if a==0
      continue
    end
    emb=signs(K(a),p)
    t=S([emb[x]==1 ? 0 : 1 for x in collect(keys(emb))])
    if !Hecke.haspreimage(mu, t)[1]
      push!(s, t)
      push!(g, a)
      u, mu = sub(S, s)
      if order(u) == order(S)
        break
      end
    else
      cnt += 1
      if cnt > 100
        b *= 2
        cnt = 0
      end
    end
  end
  hS = Hecke.GrpAbFinGenMap(S, S, vcat([x.coeff for x=s]))   # Change of coordinates so that the canonical basis elements are mapped to the elements found above
  r = elem_type(O)[]
  for i=1:length(p)
    y = haspreimage(hS,S[i])[2]
    push!(r, prod([g[i]^Int(y[i]) for i=1:length(p)]))
  end
  
  function exp(A::GrpAbFinGenElem)
    s=O(1)
    for i=1:length(p)
      if Int(A.coeff[1,i]) == 1
        s=s*r[i]
      end 
    end
    return s
  end 

  function log(B::nf_elem)
    emb=Hecke.signs(B,p)
    return S([emb[x]==1 ? 0 : 1 for x in collect(keys(emb))])
  end 
  
  function log(B::FacElem{nf_elem})
    emb=Hecke.signs(B,p)
    return S([emb[x]==1 ? 0 : 1 for x in collect(keys(emb))])
  end 
  
  return S,log,exp

end



doc"""
***
    direct_product(G::GrpAbFinGen, H::GrpAbFinGen) -> GrpAbFinGen
> Return the abelian group $G\times H$

"""

function direct_product(G::GrpAbFinGen, H::GrpAbFinGen) 

  A=vcat(rels(G), MatrixSpace(FlintZZ, rows(rels(H)), cols(rels(G)))())
  B=vcat(MatrixSpace(FlintZZ, rows(rels(G)), cols(rels(H)))(),rels(H))
 
  return AbelianGroup(hcat(A,B))
  
end 

mutable struct MapRayClassGrp{T} <: Map{T, Hecke.NfOrdIdlSet}
  header::Hecke.MapHeader
  modulus_fin::NfOrdIdl
  modulus_inf::Array{InfPlc,1}
  
  function MapRayClassGrp{T}() where {T}
    return new{T}()
  end
end

doc"""
***
    ray_class_group(m::NfOrdIdl, A::Array{InfPlc,1}=[]) -> FinGenGrpAb, Map

> Compute the ray class group of the maximal order $L$ with respect to the modulus given by $m$ (the finite part) and the infinite primes of $A$
> and return an abstract group isomorphic to the ray class group with a map 
> from the group to the ideals of $L$

"""
function ray_class_group(m::NfOrdIdl, primes::Array{InfPlc,1}=InfPlc[])

#
# We compute the group using the sequence U -> (O/m)^* _> Cl^m -> Cl -> 1
# First of all, we compute all these groups with their own maps
#  
  O=parent(m).order
  K=nf(O)
  

  C, mC = class_group(O)
  mC=_coprime_ideal(C,mC,m)
  U, mU = unit_group(O)
  M, pi= quo(O,m)
  G, mG=unit_group(M)
  
  p = [ x for x in primes if isreal(x) ]
  if !isempty(p)
    H,lH,eH=_infinite_primes(O,p,m)
    T=G
    G=direct_product(G,H)
  end

#
# We start to construct the relation matrix
#
  RG=rels(G)
  RC=rels(C)

  A=vcat(RC, MatrixSpace(FlintZZ, ngens(G)+ngens(U), cols(RC))())
  B=vcat(MatrixSpace(FlintZZ, ngens(C), cols(RG))(), RG)
  B=vcat(B, MatrixSpace(FlintZZ, ngens(U) , cols(RG))())
 
#
# We compute the relation matrix given by the image of the map U -> (O/m)^*
#
  for i=1:ngens(U)
    u=mU(U[i])
    a=(mG\(pi(u))).coeff
    if !isempty(primes)
      a=hcat(a, (lH(K(u))).coeff)
    end 
    for j=1:ngens(G)
      B[i+rows(RC)+rows(RG),j]=a[1,j]
    end
  end 

#
# We compute the relation between generators of Cl and (O/m)^* in Cl^m
#

  for i=1: ngens(C)
    if order(C[i])!=1
      y=Hecke.principal_gen((mC(C[i]))^(Int(order(C[i]))))
      b=(mG\(pi(y))).coeff
      if primes != []
        b=hcat(b, (lH(K(y))).coeff)
      end 
      for j=1: ngens(G)
        B[i,j]=-b[1,j]
      end 
    end
  end

  R=hcat(A,B)
  X=AbelianGroup(R)

#
# Discrete logarithm
#

  function disclog(J::NfOrdIdl)

    !iscoprime(J,m) && error("The ideal is not coprime to the modulus")
    if isone(J)
      return X([0 for i=1:ngens(X)])
    else
      L=mC\J
      s=mC(L)
      I= J // s
      simplify(I)
      gamma=Hecke.principal_gen(I.num)
      y=((mG\(pi(gamma)))-(mG\(pi(O(I.den))))).coeff
      if primes!=[]
        z=lH(K(gamma))
        y=hcat(y, z.coeff)
      end 
      return X(hcat(L.coeff,y))
    end
  end 

#
# Exp map
#


  function expo(a::GrpAbFinGenElem)
    b=C([a.coeff[1,i] for i=1:ngens(C)])
    if isempty(primes)
      c=G([a.coeff[1,i] for i=ngens(C)+1:ngens(X)])
      return mC(b)*(pi\(mG(c)))
    else 
      c=T([a.coeff[1,i] for i=ngens(C)+1:ngens(T)+ngens(C)])
      d=H([a.coeff[1,i] for i=ngens(T)+ngens(C)+1: ngens(X)])
      el=pi\(mG(c))
      # I need to modify $el$ so that it has the correct sign at the embeddings contained in primes
      vect=(lH(K(el))).coeff
      if vect==d.coeff
        return el*mC(b)
      else 
        correction=O(1)
        for i=1:ngens(H)
          if d.coeff[1,i]==1
            correction=correction*eH(H[i])
          end
        end
        while vect!=d.coeff
          el=el+correction
          vect=(lH(K(el))).coeff
        end
        return el*mC(b)
      end 
    end
  end 

  mp=MapRayClassGrp{typeof(X)}()
  mp.header = Hecke.MapHeader(X, Hecke.NfOrdIdlSet(O), expo, disclog)
  mp.modulus_fin=m
  mp.modulus_inf=p
 
  return X, mp
  
end
