
#!/usr/bin/python3

from speclib import *
from curve25519 import felem_t, to_felem, fadd, fsub, fmul, fsqr, finv, serialized_scalar_t, serialized_point_t, scalar_t, p25519
from sha2 import sha512

# Define prime field
d25519 : felem_t = to_felem(37095705934669439343138083508754565189542113879843219016388785533085940283555)
q25519 : felem_t = to_felem((1 << 252) + 27742317777372353535851937790883648493)

def sha512_modq(s:vlbytes) -> felem_t: 
    h = sha512(s)
    return (to_felem(bytes.to_nat_le(h) % q25519))


affine_point_t = tuple2(felem_t, felem_t)
extended_point_t = tuple4(felem_t, felem_t, felem_t, felem_t)

def point_add(p:extended_point_t,q:extended_point_t) -> extended_point_t:
  if p == (0, 1, 1, 0):
    return q
  if q == (0, 1, 1, 0):
    return p   
  (x1, y1, z1, t1) = p
  (x2, y2, z2, t2) = q
  a = fmul(fsub(y1,x1),fsub(y2,x2))
  b = fmul(fadd(y1,x1),fadd(y2,x2))
  c = fmul(to_felem(2),fmul(fmul(d25519,t1),t2))
  d = fmul(2,fmul(z1,z2))
  e = fsub(b,a)
  f = fsub(d,c)
  g = fadd(d,c)
  h = fadd(b,a)
  x3 = fmul(e,f)
  y3 = fmul(g,h)
  t3 = fmul(e,h)
  z3 = fmul(f,g)
  p = (x3, y3, z3, t3)
  return p

def point_double(p:extended_point_t) -> extended_point_t:
  if p == (0, 1, 1, 0):
    return p
  (x1, y1, z1, t1) = p
  a = fmul(x1,x1)
  b = fmul(y1,y1)
  c = fmul(to_felem(2),fmul(z1,z1))
  h = fadd(a,b)
  e = fsub(h,fmul(fadd(x1,y1),fadd(x1,y1)))
  g = fsub(a,b)
  f = fadd(c,g)
  x3 = fmul(e,f)
  y3 = fmul(g,h)
  t3 = fmul(e,h)
  z3 = fmul(f,g)
  return (x3, y3, z3, t3)

def montgomery_ladder(k:scalar_t, init: extended_point_t) -> extended_point_t:
    p0 : extended_point_t = (0, 1, 1, 0)
    p1 : extended_point_t = init
    for i in range(256):
      if k[255-i] == bit(1):
        (p0, p1) = (p1, p0)
      xx = point_double(p0)
      xp1 = point_add(p0, p1)
      if k[255-i] == bit(1):
        (p0, p1) = (xp1, xx)
      else:
        (p0, p1) = (xx, xp1)
    return p0        


def point_mul(s:serialized_scalar_t,p:extended_point_t) -> extended_point_t:
    s_ = bitvector(bytes.to_nat_le(s),256)
    Q : extended_point_t = (0, 1, 1, 0)
    Q1 = montgomery_ladder(s_, p) 
    return Q1 

def point_compress(p:extended_point_t) -> serialized_point_t :
    (px, py, pz, pt) = p 
    zinv = finv(pz)
    x = fmul(px,zinv)
    y = fmul(py,zinv)
    r = nat_t(2**255 * (x % 2) + y)
    return bytes.from_nat_le(r)

fsqrt_m1 : felem_t = to_felem(pow(2,((p25519 - 1) // 4),p25519))

def recover_x_coordinate(y:nat,sign:bool) -> felem_t:
    if y >= p25519:
        return None
    else:
        y = to_felem(y)
        p1 = fmul(d25519, fsqr(y))
        p1_1 = fadd (p1, 1) 
        x2 = fmul (fsub(fsqr(y),1), finv(p1_1))
        if x2 == 0 and sign:
            return None
        elif x2 == 0 and not sign:
            return to_felem(0)
        else:
            x = pow(x2,(p25519 + 3)//8,p25519)
            if (fsub(fsqr(x),x2) != 0):
                x = fmul(x,fsqrt_m1)
            if (fsub(fsqr(x),x2) != 0):
                return None
            else:
                if (x % 2 == 1) != sign:
                    return to_felem(p25519 - x)
                else:
                    return x
                      

def point_decompress(s:serialized_point_t) -> extended_point_t :
    y = bytes.to_nat_le(s)
    sign = (y // (1 << 255)) % 2 == 1 
    y = y % (1 << 255)
    x = recover_x_coordinate(y,sign)
    if x is None:
        return None
    else:
        return (x, y % p25519, 1, fmul(x,y % p25519))


def expand_secret(s:serialized_scalar_t) -> tuple2(serialized_scalar_t,serialized_scalar_t) :
    h = sha512(s)
    h_low = h[0:32]
    h_high= h[32:64]
    h_low[0] &= uint8(0xf8)
    h_low[31] &= uint8(127)
    h_low[31] |= uint8(64)
    return (h_low,h_high)


_g_x : felem_t = to_felem(15112221349535400772501151409588531511454012693041857206046113283949847762202)
_g_y : felem_t = to_felem(46316835694926478169428394003475163141307993866256225615783033603165251855960)

g_ed25519: extended_point_t = (_g_x,_g_y,1,fmul(_g_x,_g_y))

sigval_t = bytes_t(64)

def private_to_public(s:serialized_scalar_t) -> serialized_point_t:
    (a,_) = expand_secret(s)
    return point_compress(point_mul(s,g_ed25519))

def sign(priv:serialized_scalar_t,msg:vlbytes_t) -> sigval_t :
    (a,prefix) = expand_secret(priv)
    ap = point_compress(point_mul(a,g_ed25519))
    tmp = array.create(array.length(msg)+64,uint8(0))
    tmp[32:64] = prefix
    tmp[64:] = msg
    pmsg = tmp[32:]
    r = sha512_modq(pmsg)
    rp = point_compress(point_mul(bytes.from_nat_le(r),g_ed25519))
    tmp[0:32] = rp
    tmp[32:64] = ap
    h = sha512_modq(tmp)
    s = (r + ((h * bytes.to_nat_le(a)) % q25519)) % q25519
    tmp[32:64] = bytes.from_nat_le(nat(s))
    return tmp[0:64]

def point_equal(p:extended_point_t,q:extended_point_t) -> bool :
    (px, py, pz, pt) = p 
    (qx, qy, qz, qt) = q
    return ((fmul(px,qz) == fmul(qx,pz)) and fmul(py,qz) == fmul(qy,pz))

def verify(pub:serialized_point_t,msg:vlbytes,sigval:sigval_t) -> bool:
    ap = point_decompress(pub)
    if ap is None:
        return False
    rs = sigval[0:32]
    rp = point_decompress(rs)
    if rp is None:
        return False
    s = bytes.to_nat_le(sigval[32:64])
    if s >= q25519:
        return False
    else:
        tmp = array.create(array.length(msg)+64,uint8(0))
        tmp[0:32] = rs
        tmp[32:64] = pub
        tmp[64:] = msg
        h = sha512_modq(tmp)
        sB = point_mul(bytes.from_nat_le(s),g_ed25519)
        hA = point_mul(bytes.from_nat_le(h),ap)
        return point_equal(sB,point_add(rp,hA))
        
