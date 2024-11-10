from Crypto.Util.number import getPrime, bytes_to_long, long_to_bytes
from Crypto.Cipher import AES
from Crypto.Util import Counter
import os 
import secrets 

class EllipticCurve:
    def __init__(self):
        """
        Initializes the curve with secp384r1.
        """
        self.a = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffc
        self.b = 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef
        self.p = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff
        self.n = 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973
        self.G = (0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7, 0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f)
        self.h = 1

    def is_valid(self, x, y):
        """
        Checks if the point (x, y) is on the curve.
        """
        return (y ** 2 - x ** 3 - self.a * x - self.b) % self.p == 0
    
    def add(self, P, Q):
        """
        Adds two points P and Q.
        """
        if P == (0, 0):
            return Q
        
        if Q == (0, 0):
            return P
        
        if P[0] == Q[0] and P[1] == -Q[1] % self.p:
            return (0, 0)
        
        if P == Q:
            m = (3 * P[0] ** 2 + self.a) * pow(2 * P[1], -1, self.p)
        else:
            m = (Q[1] - P[1]) * pow(Q[0] - P[0], -1, self.p)

        x = (m ** 2 - P[0] - Q[0]) % self.p

        y = (m * (P[0] - x) - P[1]) % self.p

        return (x, y)
    
    def mul(self, n, P):
        """
        Multiplies a point P by n.
        """
        R = (0, 0)
        for i in range(n.bit_length()):
            if n & (1 << i):
                R = self.add(R, P)
            P = self.add(P, P)
        return R
    
    def gen_key(self):
        """
        Generates a key pair.
        d should be smaller than the order of the curve to prevent attacks and key collision.
        """
        d = secrets.randbelow(self.n)
        Q = self.mul(d, self.G)
        return d, Q
    
    def get_shared_secret(self, d, Q):
        """
        Generates a shared secret.
        Ensures that Q lies on the curve to prevent invalid curve attacks.
        """
        if not self.is_valid(Q[0], Q[1]):
            raise ValueError("Invalid point.")
        
        return self.mul(d, Q)
    
class Field(object):
    """
    Defines a binary field with 128 bits with custom irreducible polynomial.
    """
    # x^128 + x^127 + x^126 + x^121 + 1
    _MOD = sum((1 << a) for a in [0, 121, 126, 127, 128])

    # x^-128 is equal to x^127 + x^124 + x^121 + x^114 + 1
    _INV = sum((1 << a) for a in [0, 114, 121, 124, 127])

    @staticmethod
    def add(x, y):
        assert x < (1 << 128)
        assert y < (1 << 128)
        return x ^ y

    @staticmethod
    def mul(x, y):
        assert x < (1 << 128), x
        assert y < (1 << 128), y

        res = 0
        for bit in range(128):
            if (y >> bit) & 1:
                res ^= (2 ** bit) * x

        return Field.mod(res, Field._MOD)

    @staticmethod
    def dot(a, b):
        return Field.mul(Field.mul(a, b), Field._INV)

    @staticmethod
    def mod(a, m):
        m2 = m
        i = 0
        while m2 < a:
            m2 <<= 1
            i += 1
        while i >= 0:
            a2 = a ^ m2
            if a2 < a:
                a = a2
            m2 >>= 1
            i -= 1
        return a

class AESCipher():
    """
    AES-GCM-SIV encryption and decryption with AES-128 and AES-256.
    """
    def __init__(self, master_key=os.urandom(32), nonce=os.urandom(12)):
        """
        Initializes the AES-GCM-SIV object with a master key and nonce.
        """
        self.master_key = master_key
        self.nonce = nonce

    def derive_key(self):
        """
        Derives the authentication and encryption keys from the master key and nonce.
        If the master key is 16-byte, the function derives AES-128 keys.
        If the master key is 32-byte, the function derives AES-256 keys.
        """
        auth_key = AES.new(self.master_key, AES.MODE_ECB).encrypt(int.to_bytes(0, 4, 'little') + self.nonce)[:8] + \
                    AES.new(self.master_key, AES.MODE_ECB).encrypt(int.to_bytes(1, 4, 'little') + self.nonce)[:8]
        
        enc_key = AES.new(self.master_key, AES.MODE_ECB).encrypt(int.to_bytes(2, 4, 'little') + self.nonce)[:8] + \
                    AES.new(self.master_key, AES.MODE_ECB).encrypt(int.to_bytes(3, 4, 'little') + self.nonce)[:8]
        
        if len(self.master_key) == 32:
            enc_key += AES.new(self.master_key, AES.MODE_ECB).encrypt(int.to_bytes(4, 4, 'little') + self.nonce)[:8] + \
                        AES.new(self.master_key, AES.MODE_ECB).encrypt(int.to_bytes(5, 4, 'little') + self.nonce)[:8]
            
        return auth_key, enc_key
    
    def pad(self, data, block_len=16, pkcs7=False):
        """
        Pads the data to the block length using either PKCS7 or zero padding method.
        """
        pad_len = block_len - len(data) % block_len
        return data + bytes([pad_len] * pad_len) if pkcs7 else data + bytes([0] * pad_len)

    def polyval(self, auth_key, data):
        """
        Calculates the POLYVAL value for AES-GCM-SIV.
        """
        blocks = [data[i:i + 16] for i in range(0, len(data), 16)]
        auth_key = bytes_to_long(auth_key[::-1])
        polyval_result = 0

        for block in blocks:
            block = self.pad(block, 16)
            polyval_result = Field.dot(Field.add(polyval_result, bytes_to_long(block[::-1])), auth_key)

        return long_to_bytes(polyval_result, 16)[::-1]

    def encrypt(self, plaintext, aad):
        """
        Encrypts the plaintext and authenticates the AAD.
        """
        if len(plaintext) > 2 ** 36:
            raise Exception('Invalid plaintext')
        
        if len(aad) > 2 ** 36:
            raise Exception('Invalid AAD')
        
        auth_key, enc_key = self.derive_key()
        plaintext_pad = self.pad(plaintext)
        aad_pad = self.pad(aad)

        length_block = aad_pad + plaintext_pad + int.to_bytes(len(aad) * 8, 8, 'little') + int.to_bytes(len(plaintext) * 8, 8, 'little')
        block = self.polyval(auth_key, length_block)
        
        block = [block[i] ^ self.nonce[i] for i in range(12)] + [x for x in block[12:]]
        block[15] &= 0x7F

        tag = AES.new(auth_key, AES.MODE_ECB).encrypt(bytes(block))

        counter_block = [x for x in tag]
        counter_block[15] |= 0x80

        ctr = Counter.new(128, initial_value=int.from_bytes(bytes(counter_block), byteorder='big'))

        return AES.new(enc_key, AES.MODE_CTR, counter=ctr).encrypt(plaintext) + tag

    def decrypt(self, ciphertext, aad):
        """
        Decrypts the plaintext and authenticates the AAD.
        """
        if len(ciphertext) < 16 or len(ciphertext) > 2 ** 36 + 16:
            raise Exception('Invalid ciphertext')
        
        if len(aad) > 2 ** 36:
            raise Exception('Invalid AAD')
        
        auth_key, enc_key = self.derive_key()
        tag = ciphertext[-16:]

        counter_block = [x for x in tag]
        counter_block[15] |= 0x80

        ctr = Counter.new(128, initial_value=int.from_bytes(bytes(counter_block), byteorder='big'))
        plaintext = AES.new(enc_key, AES.MODE_CTR, counter=ctr).decrypt(ciphertext[:-16])

        plaintext_pad = self.pad(plaintext)
        aad_pad = self.pad(aad)

        length_block = aad_pad + plaintext_pad + int.to_bytes(len(aad) * 8, 8, 'little') + int.to_bytes(len(plaintext) * 8, 8, 'little')
        block = self.polyval(auth_key, length_block)

        block = [block[i] ^ self.nonce[i] for i in range(12)] + [x for x in block[12:]]
        block[15] &= 0x7F

        correct_tag = AES.new(auth_key, AES.MODE_ECB).encrypt(bytes(block))

        assert len(tag) == len(correct_tag)
        tag_check = [x ^ y for x, y in zip(tag, correct_tag)]

        if not all(x == 0 for x in tag_check):
            raise Exception('Invalid tag')
        
        return plaintext
    
if __name__ == '__main__':
    TEST_ROUND = 5
    curve = EllipticCurve()

    for test in range(TEST_ROUND):
        dA, QA = curve.gen_key()
        dB, QB = curve.gen_key()

        shared_secret_A = curve.get_shared_secret(dA, QB)
        shared_secret_B = curve.get_shared_secret(dB, QA)

        assert shared_secret_A == shared_secret_B

        master_key = long_to_bytes(shared_secret_A[0])[:32]
        nonce = long_to_bytes(shared_secret_A[1])[:12]
        pw = long_to_bytes(shared_secret_A[1])[12:]

        cipher = AESCipher(master_key, nonce)

        for i in range(TEST_ROUND):
            plaintext = os.urandom(1337)
            enc = cipher.encrypt(plaintext, pw)
            dec = cipher.decrypt(enc, pw)

            assert plaintext == dec

    print("[+] EC-DH with AES-GCM-SIV unit test passed.")
