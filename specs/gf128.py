#!/usr/bin/python3

from speclib import *

blocksize = 16
block_t = bytes_t(16)
key_t = bytes_t(16)
tag_t = bytes_t(16)
subblock_t = refine(vlbytes_t, lambda x: vlbytes.length(x) <= 16)

# Define galois field
elem_t = bitvector_t(128)
def elem(x:nat) -> elem_t:
    return bitvector(x,128)
def elem_from_bytes(b:bytes_t(16)) -> elem_t:
    return elem(uint128.to_int(bytes.to_uint128_be(b)))
def elem_to_bytes(e:elem_t) -> bytes_t(16):
    return bytes.from_uint128_be(uint128(bitvector.to_int(e)))
irred = elem(0xE1000000000000000000000000000000)
def fadd(x:elem_t,y:elem_t) -> elem_t:
    return x ^ y
def fmul(x:elem_t,y:elem_t) -> elem_t:
    res = elem(0)
    sh = x
    for i in range(128):
        if y[127-i] != bit(0):
            res ^= sh
        if sh[0] != bit(0):
            sh = (sh >> 1) ^ irred
        else:
            sh = sh >> 1
    return res

# Define GMAC
def encode(block:subblock_t) -> elem_t:
    b = array.create(16,uint8(0))
    b[0:array.length(block)] = block
    return elem_from_bytes(b)

def decode(e:elem_t) -> block_t:
    return elem_to_bytes(e)

def update(r:elem_t,block:subblock_t,acc:elem_t) -> elem_t:
    return fmul(fadd(encode(block),acc),r)

def poly(text:vlbytes_t,r:elem_t) -> elem_t:
    blocks,last = vlarray.split_blocks(text,blocksize)
    acc = elem(0)
    for i in range(array.length(blocks)):
        acc = update(r,blocks[i],acc)
    if (array.length(last) > 0):
        acc = update(r,last,acc)
    return acc

def gmac(text:vlbytes_t,k:key_t) -> tag_t :
    s = array.create(blocksize,uint8(0))
    r = encode(k)
    a = poly(text,r)
    m = decode(fadd(a,encode(s)))
    return m
