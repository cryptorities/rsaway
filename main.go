package main

import (
	"crypto/rand"
	"fmt"
	"github.com/pkg/errors"
	"io"
	"math"
	"math/big"
	"time"
)


var (
	bigZero = big.NewInt(0)
	bigOne = big.NewInt(1)
	)

var ErrDecryption = errors.New("ErrDecryption")

var smallPrimesProduct = new(big.Int).SetUint64(16294579238595022365)

type PublicKey struct {
	N *big.Int // modulus
	E int      // public exponent
}

type PrivateKey struct {
	PublicKey            // public part.
	D         *big.Int   // private exponent
	Primes    []*big.Int // prime factors of N, has >= 2 elements.
}

func (x *PublicKey) Validate() error {
	if x.N == nil {
		return errors.New("empty N")
	}
	if x.E < 2 {
		return errors.Errorf("exponent too small: %v", x.E)
	}
	if x.E > 1<<31-1 {
		return errors.Errorf("exponent too large: %v", x.E)
	}
	return nil
}

func (x *PrivateKey) calcN() (*big.Int, error) {
	modulus := new(big.Int).Set(bigOne)
	for _, prime := range x.Primes {
		// Any primes ≤ 1 will cause divide-by-zero panics later.
		if prime.Cmp(bigOne) <= 0 {
			return nil, errors.New("crypto/rsa: invalid prime value")
		}
		modulus.Mul(modulus, prime)
	}
	return modulus, nil
}

func (x *PrivateKey) Validate() error {

	if err := x.PublicKey.Validate(); err != nil {
		return err
	}

	if privN, err := x.calcN(); err != nil && privN.Cmp(x.N) != 0 {
		return errors.New("crypto/rsa: invalid modulus")
	}

	congruence := new(big.Int)
	de := new(big.Int).SetInt64(int64(x.E))
	de.Mul(de, x.D)
	for _, prime := range x.Primes {
		pminus1 := new(big.Int).Sub(prime, bigOne)
		congruence.Mod(de, pminus1)
		if congruence.Cmp(bigOne) != 0 {
			return errors.New("crypto/rsa: invalid exponents")
		}
	}

	return nil

}

func NewPrivateKey(random io.Reader, nprimes int, bits int) (*PrivateKey, error) {


	priv := new(PrivateKey)
	priv.E = 65537

	if nprimes < 2 {
		return nil, errors.New("crypto/rsa: GenerateMultiPrimeKey: nprimes must be >= 2")
	}

	if bits < 64 {
		primeLimit := float64(uint64(1) << uint(bits/nprimes))
		// pi approximates the number of primes less than primeLimit
		pi := primeLimit / (math.Log(primeLimit) - 1)
		// Generated primes start with 11 (in binary) so we can only
		// use a quarter of them.
		pi /= 4
		// Use a factor of two to ensure that key generation terminates
		// in a reasonable amount of time.
		pi /= 2
		if pi <= float64(nprimes) {
			return nil, errors.New("crypto/rsa: too few primes of given length to generate an RSA key")
		}
	}

	primes := make([]*big.Int, nprimes)

NextSetOfPrimes:
	for {
		todo := bits
		// crypto/rand should set the top two bits in each prime.
		// Thus each prime has the form
		//   p_i = 2^bitlen(p_i) × 0.11... (in base 2).
		// And the product is:
		//   P = 2^todo × α
		// where α is the product of nprimes numbers of the form 0.11...
		//
		// If α < 1/2 (which can happen for nprimes > 2), we need to
		// shift todo to compensate for lost bits: the mean value of 0.11...
		// is 7/8, so todo + shift - nprimes * log2(7/8) ~= bits - 1/2
		// will give good results.
		if nprimes >= 7 {
			todo += (nprimes - 2) / 5
		}
		for i := 0; i < nprimes; i++ {
			var err error
			primes[i], err = rand.Prime(random, todo/(nprimes-i))
			if err != nil {
				return nil, err
			}
			todo -= primes[i].BitLen()
		}

		// Make sure that primes is pairwise unequal.
		for i, prime := range primes {
			for j := 0; j < i; j++ {
				if prime.Cmp(primes[j]) == 0 {
					continue NextSetOfPrimes
				}
			}
		}

		n := new(big.Int).Set(bigOne)
		totient := new(big.Int).Set(bigOne)
		pminus1 := new(big.Int)
		for _, prime := range primes {
			n.Mul(n, prime)
			pminus1.Sub(prime, bigOne)
			totient.Mul(totient, pminus1)
		}
		if n.BitLen() != bits {
			// This should never happen for nprimes == 2 because
			// crypto/rand should set the top two bits in each prime.
			// For nprimes > 2 we hope it does not happen often.
			continue NextSetOfPrimes
		}

		priv.D = new(big.Int)
		e := big.NewInt(int64(priv.E))
		ok := priv.D.ModInverse(e, totient)

		if ok != nil {
			priv.Primes = primes
			priv.N = n
			break
		}
	}

	return priv, nil
}

func (pub *PublicKey) Encrypt(m *big.Int) *big.Int {
	e := big.NewInt(int64(pub.E))
	return new(big.Int).Exp(m, e, pub.N)
}

// decrypt performs an RSA decryption, resulting in a plaintext integer. If a
// random source is given, RSA blinding is used.
func (priv *PrivateKey) Decrypt(c *big.Int) (m *big.Int, err error) {

	if c.Cmp(priv.N) > 0 {
		err = ErrDecryption
		return
	}

	if priv.N.Sign() == 0 {
		return nil, ErrDecryption
	}

	m = new(big.Int).Exp(c, priv.D, priv.N)

	return
}

func (priv *PrivateKey) DecryptAndCheck(c *big.Int) (m *big.Int, err error) {
	m, err = priv.Decrypt(c)
	if err != nil {
		return nil, err
	}
	check := priv.PublicKey.Encrypt(m)
	if c.Cmp(check) != 0 {
		return nil, errors.New("rsa: internal error")
	}
	return m, nil
}

const bits = 32

func IV() (*big.Int, error) {

	var randomBytes = make([]byte, bits / 8 + 1)
	rand.Read(randomBytes)
	randomBytes[0] = 2
	randomBytes[1] &= 0x7F

	m := new(big.Int)
	if err := m.GobDecode(randomBytes); err != nil {
		return nil, err
	}

	return m, nil
}

func milliseconds(d time.Duration) float64 {
	sec := d / time.Millisecond
	nsec := d % time.Millisecond
	return float64(sec) + float64(nsec)/1e6
}

func doMain() error {

	pk, err := NewPrivateKey(rand.Reader, 2, bits)
	if err != nil {
		return err
	}

	m, err := IV()
	if err != nil {
		return err
	}

	/*
	for i := 0; i < 10; i++ {

		//fmt.Printf("enc text=%v\n", m)

		c := pk.Encrypt(m)
		fmt.Printf("cipher=%v\n", c)

		/*
		m1, err := pk.DecryptAndCheck(c)
		if err != nil {
			return err
		}

		fmt.Printf("pk = %v, text=%v\n", pk.Validate(), m1)

		if m.Cmp(m1) != 0 {
			fmt.Printf("something wrong\n")
		}

		m = c
	}
*/

	t0 := time.Now()

	prev_m := pk.DetectCycle(m)

	milliseconds(time.Since(t0))

	if prev_m != nil {
		fmt.Printf("FOUND prev_m=%v, enc(prev_m)=%v, m=%v, took=%0.4gms\n", prev_m, pk.Encrypt(prev_m), m, milliseconds(time.Since(t0)))
	}

	return nil

}

func main() {

	if err := doMain(); err != nil {
		fmt.Errorf("Error %v\n", err)
	}

}

func (x *PublicKey) DetectCycle(head *big.Int) *big.Int {

	next := x.one(head)

	if head.Cmp(next) == 0 {
		return head
	}

	for i, j, prev := next, x.two(head), head; i != nil && j != nil; i, j, prev = x.one(i), x.two(j), i {
		if i.Cmp(j) == 0 {
			meet := i
			if meet.Cmp(head) == 0 {
				return prev
			}
			for i, j, prev := x.one(meet), x.one(head), meet; i != nil && j != nil; i, j, prev = x.one(i), x.one(j), i {
				if i.Cmp(j) == 0 {
					return prev
				}
			}
		}
	}

	return nil

}

func (x *PublicKey) one(m *big.Int) *big.Int {
	return x.Encrypt(m)
}

func (x *PublicKey) two(m *big.Int) *big.Int {
	return x.Encrypt(x.Encrypt(m))
}
