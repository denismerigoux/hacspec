#!/usr/bin/python3

from speclib import *

# Define prime field
p25519 = (2 ** 255) - 19

felem_t = refine(nat, lambda x: x < p25519)

def to_felem(x:nat_t) -> felem_t:
    return felem_t(x % p25519)

def fadd(x:felem_t,y:felem_t) -> felem_t:
    return to_felem(x + y)

def fsub(x:felem_t,y:felem_t) -> felem_t:
    return to_felem(x - y)

def fmul(x:felem_t,y:felem_t) -> felem_t:
    return to_felem(x * y)

def fsqr(x:felem_t) -> felem_t:
    return to_felem(x * x)

def fexp(x:felem_t,n:nat_t) -> felem_t:
    return to_felem(pow(x,n,p25519))

def finv(x:felem_t) -> felem_t:
    return to_felem(pow(x,p25519-2,p25519))

point_t = tuple2(felem_t, felem_t)   #projective coordinates

scalar_t = bitvector_t(256)

g25519:point_t = (9,1)

serialized_point_t = bytes_t(32)
serialized_scalar_t = bytes_t(32)

def decodeScalar(s:serialized_scalar_t) -> scalar_t:
    k = vlbytes.copy(s)
    k[0]  &= uint8(248)
    k[31] &= uint8(127)
    k[31] |= uint8(64)
    return bitvector(bytes.to_nat_le(k),256)

def decodePoint(u:serialized_point_t) -> point_t :
    b = bytes.to_nat_le(u)
    return ((b & ((1 << 255) - 1)) % p25519,1)

def encodePoint(p:point_t) -> serialized_point_t :
    b = fmul(p[0],finv(p[1]))
    return bytes.from_nat_le(b)

def point_add_and_double(q:point_t,nq:point_t,nqp1:point_t) -> tuple2(point_t,point_t):
  (x_1, _) = q
  (x_2, z_2) = nq
  (x_3, z_3) = nqp1
  a  = fadd(x_2 ,z_2)
  aa = fsqr(a)
  b  = fsub(x_2,z_2)
  bb = fsqr(b)
  e  = fsub(aa, bb)
  c  = fadd(x_3,z_3)
  d  = fsub(x_3,z_3)
  da = fmul(d,a)
  cb = fmul(c,b)
  x_3 = fsqr(fadd(da,cb))
  z_3 = fmul(x_1,(fsqr(fsub(da,cb))))
  x_2 = fmul(aa,bb)
  z_2 = fmul(e,fadd(aa,fmul(felem_t(121665),e)))
  return ((x_2, z_2), (x_3, z_3))

def montgomery_ladder(k:scalar_t,init:point_t) -> point_t :
    p0 : point_t = (1,0)
    p1 : point_t = init
    for i in range(256):
        if k[255-i] == bit(1):
            (p1,p0) = point_add_and_double(init,p1,p0)
        else:
            (p0,p1) = point_add_and_double(init,p0,p1)
    return(p0)

def scalarmult(s:serialized_scalar_t,p:serialized_point_t) -> serialized_point_t:
    s_ = decodeScalar(s)
    p_ = decodePoint(p)
    r = montgomery_ladder(s_,p_)
    return encodePoint(r)

# ECDH API: we assume a key generation function that generates 32 random bytes for serialized_scalar_t

def is_on_curve(s:serialized_point_t) -> bool:
    return true # TODO FIX

def private_to_public(s:serialized_scalar_t) -> serialized_point_t:
    return scalarmult(s,g25519)

def ecdh_shared_secret(private:serialized_scalar_t,public:serialized_point_t) -> serialized_point_t:
    if is_on_curve(public):
        return scalarmult(private,public)
    else:
        fail("public key is not on curve")

