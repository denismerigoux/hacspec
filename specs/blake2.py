from speclib import *

variant = refine(nat, lambda x: x == 0 or x == 1)
index_t = range_t(0,16)
_SIGMA: array_t(index_t, 16 * 12) = array([
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3,
        11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4,
        7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8,
        9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13,
        2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9,
        12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11,
        13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10,
        6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5,
        10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0,
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3
    ])

def highbits_128(x:uint128_t):
    return uint64(x >> 64)
def highbits_64(x:uint64_t):
    return uint32(x >> 32)
def word_t(v:variant):
    if v == 0:
        ty = uint64_t
    else:
        ty = uint32_t
    return ty

def double_word_t(v:variant):
    if v == 0:
        ty = uint128_t
    else:
        ty = uint64_t
    return ty

def word_bits(v:variant):
    if v == 0:
        b = 64
    else:
        b = 32
    return b

def to_word(v:variant):
    if v == 0:
        f = uint64
    else:
        f = uint32
    return f

def to_words_le(v:variant):
    if v == 0:
        f = vlbytes.to_uint64s_le
    else:
        f = vlbytes.to_uint32s_le
    return f

def from_words_le(v:variant):
    if v == 0:
        f = vlbytes.from_uint64s_le
    else:
        f = vlbytes.from_uint32s_le
    return f

def rounds_in_f(v:variant):
    if v == 0:
        r =  12
    else:
        r = 10
    return r

def block_bytes(v:variant):
    if v == 0:
        bb = 128
    else:
        bb = 64
    return bb

def _R(v:variant):
    if v == 0:
        t = (32,24,16,63)
    else:
        t = (16,12,8,7)
    return t

def _IV(v:variant):
    if v == 0:
        iv = array([
            uint64(0x6A09E667F3BCC908), uint64(0xBB67AE8584CAA73B),
            uint64(0x3C6EF372FE94F82B), uint64(0xA54FF53A5F1D36F1),
            uint64(0x510E527FADE682D1), uint64(0x9B05688C2B3E6C1F),
            uint64(0x1F83D9ABFB41BD6B), uint64(0x5BE0CD19137E2179)
        ])
    else:
        iv = array([
            uint32(0x6A09E667), uint32(0xBB67AE85),
            uint32(0x3C6EF372), uint32(0xA54FF53A),
            uint32(0x510E527F), uint32(0x9B05688C),
            uint32(0x1F83D9AB), uint32(0x5BE0CD19)
        ])
    return iv


def high_bits(v:variant):
    if v == 0:
        f = highbits_128
    else:
        f = highbits_64
    return f

def to_double_word(v:variant):
    if v == 0:
        f = uint128
    else:
        f = uint64
    return f

def working_vector_t(v:variant):
    return array_t(word_t(v),16)

def hash_vector_t(v:variant):
    return array_t(word_t(v), 8)

def max_size_t(v:variant):
    return (2 ** word_bits(v) - 1)

def minus_one(v:variant):
    return (to_word(v))(max_size_t(v))

def data_internal_t(v:variant):
    return refine(bytes_t,
                  lambda x: array.length(x) < 2 ** word_bits(v)
                            and (array.length(x) % block_bytes(v) == 0))

def key_t(v:variant):
    return refine(vlbytes_t, lambda x: array.length(x) <= word_bits(v))

def key_size_t(v:variant):
    return refine(nat, lambda x: x <= word_bits(v))

def out_size_t(v:variant):
    return refine(nat, lambda x: x <= word_bits(v))


def low_bits(v:variant):
    return to_word(v)

def data_t(v:variant):
    return refine(vlbytes_t, lambda x: vlbytes.length(x)
                        < max_size_t(v) - 2 * block_bytes(v))

def blake2(var:variant):
    def _G(v: working_vector_t(var), a: index_t, b: index_t, c: index_t, d: index_t, x: word_t(var), y: word_t(var)) -> working_vector_t(var):
        (_R1,_R2,_R3,_R4) = _R(var)
        v[a] = v[a] + v[b] + x
        v[d] = word_t(var).rotate_right(v[d] ^ v[a], _R1)
        v[c] = v[c] + v[d]
        v[b] = word_t(var).rotate_right(v[b] ^ v[c], _R2)
        v[a] = v[a] + v[b] + y
        v[d] = word_t(var).rotate_right(v[d] ^ v[a], _R3)
        v[c] = v[c] + v[d]
        v[b] = word_t(var).rotate_right(v[b] ^ v[c], _R4)
        return v

    def _F(h: hash_vector_t(var), m: working_vector_t(var), t: double_word_t(var), flag: bool) -> hash_vector_t(var):
        v = array.create(16, to_word(var)(0))
        v[0:8] = h
        v[8:16] = _IV(var)
        v[12] = v[12] ^ low_bits(var)(t)
        v[13] = v[13] ^ high_bits(var)(t >> 64)
        if flag == True:
            v[14] = v[14] ^ minus_one(var)
        for i in range(rounds_in_f(var)):
            s = _SIGMA[i * 16:(i + 1) * 16]
            v = _G(v, 0, 4, 8, 12, m[s[0]], m[s[1]])
            v = _G(v, 1, 5, 9, 13, m[s[2]], m[s[3]])
            v = _G(v, 2, 6, 10, 14, m[s[4]], m[s[5]])
            v = _G(v, 3, 7, 11, 15, m[s[6]], m[s[7]])
            v = _G(v, 0, 5, 10, 15, m[s[8]], m[s[9]])
            v = _G(v, 1, 6, 11, 12, m[s[10]], m[s[11]])
            v = _G(v, 2, 7, 8, 13, m[s[12]], m[s[13]])
            v = _G(v, 3, 4, 9, 14, m[s[14]], m[s[15]])
        for i in range(8):
            h[i] = h[i] ^ v[i] ^ v[i + 8]
        return h

    def blake2_internal(data: data_internal_t(var),
               input_bytes: uint128_t,
               kk: key_size_t(var),
               nn: out_size_t) \
            -> contract(vlbytes_t,
                        lambda data, input_bytes, kk, nn: True,
                        lambda data, input_bytes, kk, nn, res: array.length(res) == nn):
        h = array.copy(_IV(var))
        h[0] = h[0] ^ to_word(var)(0x01010000) ^ (to_word(var)(kk) << 8) ^ to_word(var)(nn)
        bb = block_bytes(var)
        data_blocks = array.length(data) // bb
        if data_blocks > 1:
            for i in range(data_blocks - 1):
                h = _F(h, to_words_le(var)(
                    data[bb * i:bb * (i + 1)]), to_double_word(var)((i + 1) * bb), False)
        if kk == 0:
            h = _F(h, to_words_le(var)(
                data[bb * (data_blocks - 1):bb * data_blocks]), to_double_word(var)(input_bytes), True)
        else:
            h = _F(h, to_words_le(var)(
                data[bb * (data_blocks - 1):bb * data_blocks]), to_double_word(var)(input_bytes + bb), True)
        return from_words_le(var)(h)[:nn]

    def blake2(data: data_t(var), key: key_t(var), nn: out_size_t(var)) \
            -> contract(vlbytes_t,
                        lambda data, key, nn: True,
                        lambda data, key, nn, res: array.length(res) == nn):
        ll = array.length(data)
        kk = array.length(key)
        bb = block_bytes(var)
        data_blocks = (ll - 1) // bb + 1
        padded_data_length = data_blocks * bb
        if kk == 0:
            padded_data = array.create(padded_data_length, uint8(0))
            padded_data[:ll] = data
        else:
            padded_data = array.create(padded_data_length + bb, uint8(0))
            padded_data[0:kk] = key
            padded_data[bb:bb+ll] = key
        return blake2_internal(padded_data, ll, kk, nn)
    return blake2

blake2s = blake2(variant(1))
blake2b = blake2(variant(0))
