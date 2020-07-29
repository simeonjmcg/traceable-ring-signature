const q = 0xFFFFFFFFFFFFFFFFC90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B139B22514A08798E3404DDEF9519B3CD3A431B302B0A6DF25F14374FE1356D6D51C245E485B576625E7EC6F44C42E9A637ED6B0BFF5CB6F406B7EDEE386BFB5A899FA5AE9F24117C4B1FE649286651ECE45B3DC2007CB8A163BF0598DA48361C55D39A69163FA8FD24CF5F83655D23DCA3AD961C62F356208552BB9ED529077096966D670C354E4ABC9804F1746C08CA18217C32905E462E36CE3BE39E772C180E86039B2783A2EC07A28FB5C55DF06F4C52C9DE2BCBF6955817183995497CEA956AE515D2261898FA051015728E5A8AACAA68FFFFFFFFFFFFFFFFn;
const g = 2n;
const y = [];

const sha256 = function sha256(ascii) {
  function rightRotate(value, amount) {
    return (value>>>amount) | (value<<(32 - amount));
  };

  const maxWord = Math.pow(2, 32);
  let result = '';

  let words = [];
  const asciiBitLength = ascii.length*8;

  let hash = sha256.h = sha256.h || [];
  // Round constants: first 32 bits of the fractional parts of the cube roots of the first 64 primes
  let k = sha256.k = sha256.k || [];
  let primeCounter = k.length;

  let isComposite = {};
  for (let candidate = 2; primeCounter < 64; candidate++) {
    if (!isComposite[candidate]) {
      for (let i = 0; i < 313; i += candidate) {
        isComposite[i] = candidate;
      }
      hash[primeCounter] = (Math.pow(candidate, .5)*maxWord)|0;
      k[primeCounter++] = (Math.pow(candidate, 1/3)*maxWord)|0;
    }
  }

  ascii += '\x80' // Append Ƈ' bit (plus zero padding)
  while (ascii.length%64 - 56) ascii += '\x00' // More zero padding
  for (let i = 0; i < ascii.length; i++) {
    let j = ascii.charCodeAt(i);
    if (j>>8) return undefined; // ASCII check: only accept characters in range 0-255
    words[i>>2] |= j << ((3 - i)%4)*8;
  }
  words[words.length] = ((asciiBitLength/maxWord)|0);
  words[words.length] = (asciiBitLength)

  // process each chunk
  for (let j = 0; j < words.length;) {
    let w = words.slice(j, j += 16); // The message is expanded into 64 words as part of the iteration
    let oldHash = hash;
    // This is now the undefinedworking hash", often labelled as let a...g
    // (we have to truncate as well, otherwise extra entries at the end accumulate
    hash = hash.slice(0, 8);

    for (let i = 0; i < 64; i++) {
      let i2 = i + j;
      // Expand the message into 64 words
      // Used below if 
      let w15 = w[i - 15], w2 = w[i - 2];

      // Iterate
      let a = hash[0], e = hash[4];
      let temp1 = hash[7]
        + (rightRotate(e, 6) ^ rightRotate(e, 11) ^ rightRotate(e, 25)) // S1
        + ((e&hash[5])^((~e)&hash[6])) // ch
        + k[i]
      // Expand the message schedule if needed
        + (w[i] = (i < 16) ? w[i] : (
          w[i - 16]
          + (rightRotate(w15, 7) ^ rightRotate(w15, 18) ^ (w15>>>3)) // s0
          + w[i - 7]
          + (rightRotate(w2, 17) ^ rightRotate(w2, 19) ^ (w2>>>10)) // s1
        )|0
        );
      // This is only used once, so *could* be moved below, but it only saves 4 bytes and makes things unreadble
      let temp2 = (rightRotate(a, 2) ^ rightRotate(a, 13) ^ rightRotate(a, 22)) // S0
        + ((a&hash[1])^(a&hash[2])^(hash[1]&hash[2])); // maj

      hash = [(temp1 + temp2)|0].concat(hash); // We don't bother trimming off the extra ones, they're harmless as long as we're truncating when we do the slice()
      hash[4] = (hash[4] + temp1)|0;
    }

    for (let i = 0; i < 8; i++) {
      hash[i] = (hash[i] + oldHash[i])|0;
    }
  }

  for (let i = 0; i < 8; i++) {
    for (let j = 3; j + 1; j--) {
      let b = (hash[i]>>(j*8))&255;
      result += ((b < 16) ? 0 : '') + b.toString(16);
    }
  }
  return BigInt("0x" + result);
};

function mod(n, p) {
  return ((n % p) + p) % p;
}

function powMod(x, y, p) {
  let res = 1n;
  x = x % p;
  if (x == 0n) return 0n;
  while (y > 0n) {
    if (y & 1n) res = (res*x) % p;

    y >>= 1n;
    x = (x*x) % p;
  }
  return res;
}

function iroot(i, n) {
  const i1 = i - 1n;
  let s = n + 1n;
  let u = n;
  while (u < s) {
    s = u;
    u = ((u * i1) + n / (u ** i1)) / i;
  }
  return s;
}

function randomNumber() {
  const array = new Uint8Array(256);
  crypto.getRandomValues(array);
  // return random value as BigInt, mod q
  return array.reduce((accum, x) => BigInt(x) + accum * 256n, 0n) % q;
}

function generatePublicFromPrivate(x) {
  return powMod(g, x, q);
}

function generateKey() {
  const x_i = randomNumber();
  const y_i = generatePublicFromPrivate(x_i);
  registerKey(y_i);
  return { pub: y_i, priv: x_i };
}

function registerKey(pub) {
  y.push(pub);
}

function sign(message, x_i, y_i, issue) {
  const i = y.indexOf(y_i);
  if (i === -1) {
    throw new Error("");
  }
  const sigma = [];

  const L = `${sha256(issue)},[${y.join(",")}]`;
  const h = sha256(L);
  sigma[i] = powMod(h, x_i, q);
  const A_0 = sha256(`${L},${sha256(message)}`);
  const A_1 = iroot(BigInt(i + 1), sigma[i] / A_0);

  const z = [], a = [], b = [], c = [];

  const w_i = randomNumber();
  a[i] = powMod(g, w_i, q);
  b[i] = powMod(h, w_i, q);
  c[i] = 0;
  
  for (let j=0; j<y.length; j++) {
    if (j !== i) {
      sigma[j] = (A_0 * powMod(A_1, BigInt(j+1), q)) % q;

      z[j] = randomNumber();
      c[j] = randomNumber();
      a[j] = (powMod(g, z[j], q) * powMod(y_i, c[j], q)) % q;
      b[j] = (powMod(h, z[j], q) * powMod(sigma[j], c[j], q)) % q;
    }
  }
  c_hash = sha256(`${L},${message},${A_0},${A_1},[${a}],[${b}]`);
  c[i] = mod(c_hash - c.reduce((accu, x) => accu + x, 0), q);
  z[i] = mod(w_i - c[i] * x_i, q);
  return { A_1, c, z};
}

function verify(message, issue, A_1, c, z) {
  const L = `${sha256(issue)},[${y}]`;
  const h = sha256(L);

  const A_0 = sha256(`${L},${sha256(message)}`);
  const sigma = [];

  const a = [], b = [];

  for (let i=0; i<y.length; i++) {
    sigma[i] = (A_0 * powMod(A_1, BigInt(i + 1), q)) % q;
    a[i] = (powMod(g, z[i], q) * powMod(y[i], c[i], q)) % q;
    b[i] = (powMod(h, z[i], q) * powMod(sigma[i], c[i], q)) % q;
  }

  if(sha256(`${L},${message},${A_0},${A_1},[${a}],[${b}]`) !== mod(c.reduce((accu, x) => accu + x, 0), q)) {
    return false;
  }
  return true;
}
