import tkinter as tk
from tkinter import ttk, messagebox, font
import math
import numpy as np




# vigenere
def vigenere_encrypt(plaintext, key):
    key = key.upper(); result, ki = [], 0
    for ch in plaintext.upper():
        if ch.isalpha():
            shift = ord(key[ki % len(key)]) - ord('A')
            result.append(chr((ord(ch) - ord('A') + shift) % 26 + ord('A'))); ki += 1
        else:
            result.append(ch)
    return ''.join(result)

def vigenere_decrypt(ciphertext, key):
    key = key.upper(); result, ki = [], 0
    for ch in ciphertext.upper():
        if ch.isalpha():
            shift = ord(key[ki % len(key)]) - ord('A')
            result.append(chr((ord(ch) - ord('A') - shift) % 26 + ord('A'))); ki += 1
        else:
            result.append(ch)
    return ''.join(result)


# affin
def mod_inverse(a, m=26):
    for x in range(1, m):
        if (a * x) % m == 1:
            return x
    return None

def affine_encrypt(plaintext, a, b):
    if math.gcd(a, 26) != 1:
        raise ValueError(f"'a'={a} harus koprima dengan 26")
    result = []
    for ch in plaintext.upper():
        if ch.isalpha():
            result.append(chr((a*(ord(ch)-ord('A'))+b) % 26 + ord('A')))
        else:
            result.append(ch)
    return ''.join(result)

def affine_decrypt(ciphertext, a, b):
    if math.gcd(a, 26) != 1:
        raise ValueError(f"'a'={a} harus koprima dengan 26")
    a_inv = mod_inverse(a)
    result = []
    for ch in ciphertext.upper():
        if ch.isalpha():
            result.append(chr((a_inv*(ord(ch)-ord('A')-b)) % 26 + ord('A')))
        else:
            result.append(ch)
    return ''.join(result)


# playfair
def playfair_build_matrix(key):
    key = key.upper().replace('J','I')
    seen, matrix = set(), []
    for ch in key + 'ABCDEFGHIKLMNOPQRSTUVWXYZ':
        if ch.isalpha() and ch not in seen:
            seen.add(ch); matrix.append(ch)
    return [matrix[i*5:(i+1)*5] for i in range(5)]

def playfair_find(m, ch):
    for r in range(5):
        for c in range(5):
            if m[r][c] == ch: return r, c
    return None, None

def playfair_prepare(text):
    text = [c for c in text.upper().replace('J','I') if c.isalpha()]
    pairs = []; i = 0
    while i < len(text):
        a = text[i]; b = text[i+1] if i+1 < len(text) else 'X'
        if a == b: pairs.append((a,'X')); i += 1
        else: pairs.append((a,b)); i += 2
    return pairs

def playfair_encrypt(plaintext, key):
    m = playfair_build_matrix(key); result = []
    for a, b in playfair_prepare(plaintext):
        r1,c1 = playfair_find(m,a); r2,c2 = playfair_find(m,b)
        if r1==r2:   result += [m[r1][(c1+1)%5], m[r2][(c2+1)%5]]
        elif c1==c2: result += [m[(r1+1)%5][c1], m[(r2+1)%5][c2]]
        else:        result += [m[r1][c2], m[r2][c1]]
    return ''.join(result)

def playfair_decrypt(ciphertext, key):
    m = playfair_build_matrix(key)
    text = [c for c in ciphertext.upper() if c.isalpha()]
    pairs = [(text[i],text[i+1]) for i in range(0,len(text)-1,2)]; result = []
    for a, b in pairs:
        r1,c1 = playfair_find(m,a); r2,c2 = playfair_find(m,b)
        if r1==r2:   result += [m[r1][(c1-1)%5], m[r2][(c2-1)%5]]
        elif c1==c2: result += [m[(r1-1)%5][c1], m[(r2-1)%5][c2]]
        else:        result += [m[r1][c2], m[r2][c1]]
    return ''.join(result)


# hill cipher
def hill_mod_inverse_matrix(matrix, mod=26):
    det = int(round(np.linalg.det(matrix))) % mod
    det_inv = mod_inverse(det % mod, mod)
    if det_inv is None:
        raise ValueError("Matriks tidak memiliki invers mod 26")
    n = matrix.shape[0]; adj = np.zeros((n, n), dtype=float)
    for r in range(n):
        for c in range(n):
            minor = np.delete(np.delete(matrix,r,axis=0),c,axis=1)
            adj[c][r] = ((-1)**(r+c)) * int(round(np.linalg.det(minor)))
    return (det_inv * adj % mod).astype(int)

def hill_process(text, key_matrix):
    n = key_matrix.shape[0]
    text = [c for c in text.upper() if c.isalpha()]
    while len(text) % n: text.append('X')
    result = []
    for i in range(0, len(text), n):
        block = np.array([ord(c)-ord('A') for c in text[i:i+n]])
        enc = (key_matrix @ block) % 26
        result += [chr(int(v)+ord('A')) for v in enc]
    return ''.join(result)

def hill_encrypt(plaintext, key_matrix):  return hill_process(plaintext, key_matrix)
def hill_decrypt(ciphertext, key_matrix): return hill_process(ciphertext, hill_mod_inverse_matrix(key_matrix))

def parse_matrix(text):
    rows = [r.strip() for r in text.strip().split('\n') if r.strip()]
    m = np.array([[int(x) for x in r.split()] for r in rows])
    if m.shape[0] != m.shape[1]:
        raise ValueError("Matriks harus persegi (n×n)")
    return m


#enigma
ENIGMA_ROTORS = {
    'I':   ('EKMFLGDQVZNTOWYHXUSPAIBRCJ', 'Q'),
    'II':  ('AJDKSIRUXBLHWTMCQGZNPYFVOE', 'E'),
    'III': ('BDFHJLCPRTXVZNYEIWGAKMUSQO', 'V'),
    'IV':  ('ESOVPZJAYQUIRHXLNFTGKDCMWB', 'J'),
    'V':   ('VZBRGITYUPSDNHLXAWMJQOFECK', 'Z'),
}
ENIGMA_REFLECTOR = 'YRUHQSLDPXNGOKMIEBFZCWVJAT'
ROTOR_NAMES = ['I', 'II', 'III', 'IV', 'V']

class EnigmaMachine:
    def __init__(self, rotor_names, rotor_positions, plugboard_pairs):
        if not rotor_names:
            raise ValueError("Minimal 1 rotor")
        self.rotors = []
        for name, pos in zip(rotor_names, rotor_positions):
            wiring, notch = ENIGMA_ROTORS[name]
            self.rotors.append({'wiring': wiring, 'notch': notch,
                                 'pos': ord(pos.upper()) - ord('A')})
        self.plugboard = {}
        for pair in plugboard_pairs:
            pair = pair.upper().strip()
            if len(pair) == 2:
                self.plugboard[pair[0]] = pair[1]
                self.plugboard[pair[1]] = pair[0]

    def _plug(self, ch): return self.plugboard.get(ch, ch)

    def _step(self):
        n = len(self.rotors)
        advance = [False] * n
        advance[-1] = True  # rightmost always steps
        for i in range(n - 1, 0, -1):
            if self.rotors[i]['pos'] == ord(self.rotors[i]['notch']) - ord('A'):
                advance[i] = True      # double-step: rotor at notch steps itself
                advance[i - 1] = True  # and advances its left neighbour
        for i in range(n):
            if advance[i]:
                self.rotors[i]['pos'] = (self.rotors[i]['pos'] + 1) % 26

    def encode_char(self, ch):
        if not ch.isalpha(): return ch
        ch = ch.upper(); self._step()
        idx = ord(self._plug(ch)) - ord('A')
        for rotor in reversed(self.rotors):
            shifted = (idx + rotor['pos']) % 26
            idx = (ord(rotor['wiring'][shifted]) - ord('A') - rotor['pos']) % 26
        idx = ord(ENIGMA_REFLECTOR[idx]) - ord('A')
        for rotor in self.rotors:
            shifted = (idx + rotor['pos']) % 26
            idx = (rotor['wiring'].index(chr(shifted + ord('A'))) - rotor['pos']) % 26
        return self._plug(chr(idx + ord('A')))

    def process(self, text):
        return ''.join(self.encode_char(c) for c in text)


#theme
BG_DARK  = "#0d1117"
BG_CARD  = "#161b22"
BG_INPUT = "#1c2333"
ACCENT   = "#58a6ff"
ACCENT2  = "#3fb950"
BORDER   = "#30363d"
FG_WHITE = "#e6edf3"
FG_MUTED = "#8b949e"
FG_LABEL = "#c9d1d9"
GOLD     = "#d29922"


#main
class CryptoApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.geometry("1300x820")
        self.resizable(True, True)
        self.configure(bg=BG_DARK)

        self.f_title  = font.Font(family="Consolas", size=18, weight="bold")
        self.f_header = font.Font(family="Consolas", size=11, weight="bold")
        self.f_mono   = font.Font(family="Courier New", size=11)
        self.f_mono_s = font.Font(family="Courier New", size=10)
        self.f_lbl    = font.Font(family="Consolas", size=11)
        self.f_small  = font.Font(family="Consolas", size=9)
        self.f_btn    = font.Font(family="Consolas", size=10, weight="bold")

        self._build_styles()
        self._build_header()
        self._build_notebook()
        self._build_statusbar()


    def _build_styles(self):
        s = ttk.Style(self)
        s.theme_use('clam')
        s.configure('TNotebook', background=BG_DARK, borderwidth=0)
        s.configure('TNotebook.Tab', background=BG_CARD, foreground=FG_MUTED,
                    font=('Consolas', 10, 'bold'), padding=[20, 10], borderwidth=0)
        s.map('TNotebook.Tab',
              background=[('selected', BG_INPUT)], foreground=[('selected', ACCENT)])
        s.configure('TFrame', background=BG_DARK)
        s.configure('TCombobox', fieldbackground=BG_INPUT, background=BG_INPUT,
                    foreground=FG_WHITE, selectbackground=ACCENT,
                    selectforeground=BG_DARK, borderwidth=1, relief='flat',
                    font=('Courier New', 11))
        s.map('TCombobox', fieldbackground=[('readonly', BG_INPUT)])

    def _build_header(self):
        h = tk.Frame(self, bg=BG_CARD, height=0)
        h.pack(fill='x'); h.pack_propagate(False)


    def _build_notebook(self):
        nb = ttk.Notebook(self)
        nb.pack(fill='both', expand=True, padx=12, pady=(8, 0))
        for label, builder in [
            ("Ⅰ  Vigenere", self._tab_vigenere),
            ("Ⅱ  Affine",   self._tab_affine),
            ("Ⅲ  Playfair", self._tab_playfair),
            ("Ⅳ  Hill",     self._tab_hill),
            ("Ⅴ  Enigma",   self._tab_enigma),
        ]:
            f = ttk.Frame(nb); nb.add(f, text=label); builder(f)

    def _build_statusbar(self):
        self._sv = tk.StringVar(value="Siap.")
        bar = tk.Frame(self, bg=BG_CARD, height=28)
        bar.pack(fill='x')
        tk.Label(bar, textvariable=self._sv, font=self.f_small,
                 bg=BG_CARD, fg=FG_MUTED, anchor='w').pack(side='left', padx=16)

    def _status(self, msg): self._sv.set(msg)


    def _card(self, parent, title, col, colspan=1, row=0,
              padx=(6,6), pady=(6,6)):
        f = tk.Frame(parent, bg=BG_CARD, bd=0,
                     highlightthickness=1, highlightbackground=BORDER)
        f.grid(row=row, column=col, columnspan=colspan,
               sticky='nsew', padx=padx, pady=pady)
        if title:
            tk.Label(f, text=title, font=self.f_header,
                     bg=BG_CARD, fg=ACCENT, anchor='w').pack(fill='x', padx=14, pady=(10,2))
            tk.Frame(f, bg=BORDER, height=1).pack(fill='x', padx=14)
        return f

    def _textbox(self, parent, height=6, disabled=False):
        t = tk.Text(parent, height=height, bg=BG_INPUT, fg=FG_WHITE,
                    font=self.f_mono, bd=0, padx=10, pady=8,
                    insertbackground=ACCENT, selectbackground=ACCENT,
                    selectforeground=BG_DARK, relief='flat', wrap='word',
                    highlightthickness=1, highlightbackground=BORDER,
                    highlightcolor=ACCENT)
        t.pack(fill='both', expand=True, padx=14, pady=10)
        if disabled: t.config(state='disabled')
        return t

    def _entry(self, parent, width=18, default=''):
        e = tk.Entry(parent, font=self.f_mono, bg=BG_INPUT, fg=FG_WHITE,
                     bd=0, insertbackground=ACCENT, relief='flat',
                     highlightthickness=1, highlightbackground=BORDER,
                     highlightcolor=ACCENT, width=width)
        e.pack(side='left', ipady=5)
        if default: e.insert(0, default)
        return e

    def _btn(self, parent, text, cmd, color=ACCENT, pad_x=14, pad_y=7):
        b = tk.Button(parent, text=text, command=cmd,
                      font=self.f_btn, bg=color, fg=BG_DARK,
                      activebackground=FG_WHITE, activeforeground=BG_DARK,
                      bd=0, padx=pad_x, pady=pad_y, cursor='hand2', relief='flat')
        return b

    def _settext(self, box, text):
        box.config(state='normal')
        box.delete('1.0','end')
        box.insert('end', text)
        box.config(state='disabled')

    def _inforow(self, parent, row, colspan, text, title="Informasi"):
        c = self._card(parent, title, col=0, colspan=colspan,
                       row=row, padx=(8,8), pady=(0,8))
        tk.Label(c, text=text, font=self.f_small, bg=BG_CARD,
                 fg=FG_MUTED, justify='left', wraplength=1100,
                 anchor='w').pack(padx=14, pady=8, anchor='w')
        parent.rowconfigure(row, weight=0)

    def _keyrow(self, parent, row, colspan):
        f = tk.Frame(parent, bg=BG_DARK)
        f.grid(row=row, column=0, columnspan=colspan,
               sticky='ew', padx=8, pady=6)
        return f


    def _tab_vigenere(self, p):
        p.rowconfigure(0, weight=1)
        p.columnconfigure(0, weight=1); p.columnconfigure(1, weight=1)

        self.vig_in  = self._textbox(self._card(p,"  Teks Input",  0, row=0, padx=(8,4), pady=(8,8)))
        self.vig_out = self._textbox(self._card(p,"  Hasil Output",1, row=0, padx=(4,8), pady=(8,8)), disabled=True)

        kr = self._keyrow(p, 1, 2)
        tk.Label(kr, text="Kunci :", font=self.f_lbl, bg=BG_DARK, fg=FG_LABEL
                 ).pack(side='left', padx=(10,6))
        self.vig_key = self._entry(kr, 22, "SECRET")
        self._btn(kr," Enkripsi", self._vig_enc, ACCENT2).pack(side='left',padx=10)
        self._btn(kr," Dekripsi", self._vig_dec, ACCENT ).pack(side='left',padx=2)
        self._btn(kr,"Bersihkan",
                  lambda:(self.vig_in.delete('1.0','end'), self._settext(self.vig_out,"")),
                  BORDER).pack(side='left',padx=10)



    def _vig_enc(self):
        try:
            k=self.vig_key.get().strip()
            if not k or not k.isalpha(): raise ValueError("Kunci harus huruf alfabet")
            t=self.vig_in.get('1.0','end').strip()
            if not t: raise ValueError("Teks kosong")
            r=vigenere_encrypt(t,k); self._settext(self.vig_out,r)
            self._status(f"Vigenere enkripsi OK — {len(r)} karakter")
        except Exception as e: messagebox.showerror("Error",str(e))

    def _vig_dec(self):
        try:
            k=self.vig_key.get().strip()
            if not k or not k.isalpha(): raise ValueError("Kunci harus huruf alfabet")
            t=self.vig_in.get('1.0','end').strip()
            if not t: raise ValueError("Teks kosong")
            r=vigenere_decrypt(t,k); self._settext(self.vig_out,r)
            self._status(f"Vigenere dekripsi OK — {len(r)} karakter")
        except Exception as e: messagebox.showerror("Error",str(e))


    def _tab_affine(self, p):
        p.rowconfigure(0, weight=1)
        p.columnconfigure(0, weight=1); p.columnconfigure(1, weight=1)

        self.aff_in  = self._textbox(self._card(p,"Teks Input",  0, row=0, padx=(8,4), pady=(8,8)))
        self.aff_out = self._textbox(self._card(p,"Hasil Output",1, row=0, padx=(4,8), pady=(8,8)), disabled=True)

        kr = self._keyrow(p, 1, 2)
        tk.Label(kr, text="a (koprima 26):", font=self.f_lbl, bg=BG_DARK, fg=FG_LABEL
                 ).pack(side='left', padx=(10,6))
        self.aff_a = self._entry(kr, 6, "5")
        tk.Label(kr, text="  b (0–25):", font=self.f_lbl, bg=BG_DARK, fg=FG_LABEL
                 ).pack(side='left', padx=(14,6))
        self.aff_b = self._entry(kr, 6, "8")
        self._btn(kr," Enkripsi", self._aff_enc, ACCENT2).pack(side='left',padx=10)
        self._btn(kr," Dekripsi", self._aff_dec, ACCENT ).pack(side='left',padx=2)
        self._btn(kr,"Bersihkan",
                  lambda:(self.aff_in.delete('1.0','end'), self._settext(self.aff_out,"")),
                  BORDER).pack(side='left',padx=10)


    def _aff_enc(self):
        try:
            a,b=int(self.aff_a.get()),int(self.aff_b.get())
            t=self.aff_in.get('1.0','end').strip()
            if not t: raise ValueError("Teks kosong")
            r=affine_encrypt(t,a,b); self._settext(self.aff_out,r)
            self._status(f"Affine enkripsi OK  (a={a}, b={b})")
        except Exception as e: messagebox.showerror("Error",str(e))

    def _aff_dec(self):
        try:
            a,b=int(self.aff_a.get()),int(self.aff_b.get())
            t=self.aff_in.get('1.0','end').strip()
            if not t: raise ValueError("Teks kosong")
            r=affine_decrypt(t,a,b); self._settext(self.aff_out,r)
            self._status(f"Affine dekripsi OK  (a={a}, b={b})")
        except Exception as e: messagebox.showerror("Error",str(e))


    def _tab_playfair(self, p):
        p.rowconfigure(0, weight=1)
        p.columnconfigure(0, weight=1); p.columnconfigure(1, weight=1); p.columnconfigure(2, weight=0)

        self.pf_in  = self._textbox(self._card(p,"Teks Input",  0, row=0, padx=(8,4), pady=(8,8)))
        self.pf_out = self._textbox(self._card(p,"Hasil Output",1, row=0, padx=(4,4), pady=(8,8)), disabled=True)
        mc = self._card(p,"Matriks 5×5", 2, row=0, padx=(4,8), pady=(8,8))
        self.pf_matrix_lbl = tk.Label(mc, text="(masukkan kunci dulu)",
                                       font=font.Font(family="Courier New",size=13),
                                       bg=BG_CARD, fg=FG_MUTED, justify='left')
        self.pf_matrix_lbl.pack(padx=14, pady=12)
        self._btn(mc,"⟳ Tampilkan Matriks", self._pf_show_matrix, GOLD).pack(padx=14,pady=6)

        kr = self._keyrow(p, 1, 3)
        tk.Label(kr, text="Kunci :", font=self.f_lbl, bg=BG_DARK, fg=FG_LABEL
                 ).pack(side='left', padx=(10,6))
        self.pf_key = self._entry(kr, 22, "MONARCHY")
        self._btn(kr," Enkripsi", self._pf_enc, ACCENT2).pack(side='left',padx=10)
        self._btn(kr," Dekripsi", self._pf_dec, ACCENT ).pack(side='left',padx=2)
        self._btn(kr,"✕ Bersihkan",
                  lambda:(self.pf_in.delete('1.0','end'), self._settext(self.pf_out,"")),
                  BORDER).pack(side='left',padx=10)


    def _pf_show_matrix(self):
        key=self.pf_key.get().strip()
        if not key: messagebox.showwarning("Peringatan","Masukkan kunci dulu"); return
        m=playfair_build_matrix(key)
        self.pf_matrix_lbl.config(text='\n'.join('  '.join(row) for row in m), fg=ACCENT2)

    def _pf_enc(self):
        try:
            key=self.pf_key.get().strip()
            if not key: raise ValueError("Kunci kosong")
            t=self.pf_in.get('1.0','end').strip()
            if not t: raise ValueError("Teks kosong")
            self._settext(self.pf_out, playfair_encrypt(t,key)); self._pf_show_matrix()
            self._status("Playfair enkripsi OK")
        except Exception as e: messagebox.showerror("Error",str(e))

    def _pf_dec(self):
        try:
            key=self.pf_key.get().strip()
            if not key: raise ValueError("Kunci kosong")
            t=self.pf_in.get('1.0','end').strip()
            if not t: raise ValueError("Teks kosong")
            self._settext(self.pf_out, playfair_decrypt(t,key)); self._pf_show_matrix()
            self._status("Playfair dekripsi OK")
        except Exception as e: messagebox.showerror("Error",str(e))


    def _tab_hill(self, p):
        p.rowconfigure(0, weight=1)
        p.columnconfigure(0,weight=1); p.columnconfigure(1,weight=1); p.columnconfigure(2,weight=1)

        self.hill_in  = self._textbox(self._card(p,"  Teks Input",        0, row=0, padx=(8,4), pady=(8,8)))
        self.hill_out = self._textbox(self._card(p,"  Hasil Output",       1, row=0, padx=(4,4), pady=(8,8)), disabled=True)
        mc = self._card(p,"Matriks Kunci (n×n)", 2, row=0, padx=(4,8), pady=(8,8))
        tk.Label(mc, text="Satu baris per baris, angka dipisah spasi:",
                 font=self.f_small, bg=BG_CARD, fg=FG_MUTED).pack(padx=14,pady=(8,0),anchor='w')
        self.hill_matrix = tk.Text(mc, height=7, bg=BG_INPUT, fg=FG_WHITE,
                                    font=self.f_mono, bd=0, padx=10, pady=8,
                                    insertbackground=ACCENT, relief='flat',
                                    highlightthickness=1, highlightbackground=BORDER,
                                    highlightcolor=ACCENT)
        self.hill_matrix.pack(fill='both',expand=True,padx=14,pady=8)
        self.hill_matrix.insert('end',"6 24 1\n13 16 10\n20 17 15")

        kr = self._keyrow(p, 1, 3)
        self._btn(kr," Enkripsi", self._hill_enc, ACCENT2).pack(side='left',padx=10)
        self._btn(kr," Dekripsi", self._hill_dec, ACCENT ).pack(side='left',padx=2)
        self._btn(kr,"Bersihkan",
                  lambda:(self.hill_in.delete('1.0','end'), self._settext(self.hill_out,"")),
                  BORDER).pack(side='left',padx=10)


    def _hill_enc(self):
        try:
            mat=parse_matrix(self.hill_matrix.get('1.0','end'))
            t=self.hill_in.get('1.0','end').strip()
            if not t: raise ValueError("Teks kosong")
            r=hill_encrypt(t,mat); self._settext(self.hill_out,r)
            self._status(f"Hill enkripsi OK  ({mat.shape[0]}×{mat.shape[1]})")
        except Exception as e: messagebox.showerror("Error",str(e))

    def _hill_dec(self):
        try:
            mat=parse_matrix(self.hill_matrix.get('1.0','end'))
            t=self.hill_in.get('1.0','end').strip()
            if not t: raise ValueError("Teks kosong")
            r=hill_decrypt(t,mat); self._settext(self.hill_out,r)
            self._status(f"Hill dekripsi OK  ({mat.shape[0]}×{mat.shape[1]})")
        except Exception as e: messagebox.showerror("Error",str(e))


    def _tab_enigma(self, p):
        p.rowconfigure(0, weight=1)
        p.columnconfigure(0, weight=1)
        p.columnconfigure(1, weight=1)
        p.columnconfigure(2, weight=0)   # fixed-width config panel

        # Input / Output text areas
        self.en_in  = self._textbox(self._card(p,"  Teks Input", 0, row=0, padx=(8,4), pady=(8,8)))
        self.en_out = self._textbox(
            self._card(p,"  Hasil Output  (Enkripsi = Dekripsi)",1, row=0, padx=(4,4), pady=(8,8)),
            disabled=True)

        cfg = tk.Frame(p, bg=BG_CARD, bd=0,
                       highlightthickness=1, highlightbackground=BORDER,
                       width=360)
        cfg.grid(row=0, column=2, sticky='nsew', padx=(4,8), pady=(8,8))
        cfg.pack_propagate(False)
        cfg.grid_propagate(False)

        # Panel header
        tk.Label(cfg, text="Konfigurasi Enigma",
                 font=self.f_header, bg=BG_CARD, fg=ACCENT,
                 anchor='w').pack(fill='x', padx=16, pady=(14,4))
        tk.Frame(cfg, bg=BORDER, height=1).pack(fill='x', padx=16, pady=(0,8))

        # Scrollable inner
        canvas   = tk.Canvas(cfg, bg=BG_CARD, bd=0, highlightthickness=0)
        vscroll  = ttk.Scrollbar(cfg, orient='vertical', command=canvas.yview)
        canvas.configure(yscrollcommand=vscroll.set)
        vscroll.pack(side='right', fill='y')
        canvas.pack(side='left', fill='both', expand=True)
        inner    = tk.Frame(canvas, bg=BG_CARD)
        iwin     = canvas.create_window((0,0), window=inner, anchor='nw')

        def _resize(e=None):
            canvas.configure(scrollregion=canvas.bbox('all'))
        def _fit_width(e):
            canvas.itemconfig(iwin, width=e.width)

        inner.bind('<Configure>', _resize)
        canvas.bind('<Configure>', _fit_width)
        canvas.bind_all('<MouseWheel>',
                        lambda e: canvas.yview_scroll(int(-1*(e.delta/120)), 'units'))

        #
        self._sec(inner, " Jumlah Rotor")
        self.en_num = tk.IntVar(value=3)
        nr = tk.Frame(inner, bg=BG_CARD); nr.pack(fill='x', padx=16, pady=4)
        for n in range(1, 6):
            tk.Radiobutton(
                nr, text=f"  {n}  ", variable=self.en_num, value=n,
                command=self._enigma_refresh_ui,
                font=self.f_mono_s, bg=BG_CARD, fg=FG_WHITE,
                selectcolor=ACCENT, activebackground=BG_CARD,
                activeforeground=FG_WHITE, indicatoron=False,
                bd=0, padx=10, pady=6, cursor='hand2',
                highlightthickness=1, highlightbackground=BORDER,
                highlightcolor=ACCENT, relief='flat'
            ).pack(side='left', padx=3)

        self._sec(inner, " Rotor  (kiri → kanan) + Posisi Awal")
        self.en_rotor_rows   = []
        self.en_rotor_cbs    = []
        self.en_rotor_pos    = []
        defaults_r = ['I','II','III','IV','V']
        defaults_p = ['A','A','A','A','A']

        for i in range(5):
            row = tk.Frame(inner, bg=BG_CARD)
            row.pack(fill='x', padx=16, pady=4)

            tk.Label(row, text=f"Rotor {i+1} :", font=self.f_lbl,
                     bg=BG_CARD, fg=FG_LABEL, width=9, anchor='w').pack(side='left')

            cb = ttk.Combobox(row, values=ROTOR_NAMES, width=5,
                              state='readonly', font=self.f_mono_s)
            cb.set(defaults_r[i]); cb.pack(side='left', padx=(4,0), ipady=3)

            tk.Label(row, text="  Posisi :", font=self.f_small,
                     bg=BG_CARD, fg=FG_MUTED).pack(side='left', padx=(10,4))

            pe = tk.Entry(row, font=self.f_mono, bg=BG_INPUT, fg=FG_WHITE,
                          bd=0, insertbackground=ACCENT, relief='flat',
                          highlightthickness=1, highlightbackground=BORDER,
                          highlightcolor=ACCENT, width=4)
            pe.pack(side='left', ipady=5)
            pe.insert(0, defaults_p[i])

            self.en_rotor_rows.append(row)
            self.en_rotor_cbs.append(cb)
            self.en_rotor_pos.append(pe)

        self._sec(inner, " Plugboard  (mis: AB CD EF)")
        self.en_plug = tk.Entry(inner, font=self.f_mono, bg=BG_INPUT, fg=FG_WHITE,
                                bd=0, insertbackground=ACCENT, relief='flat',
                                highlightthickness=1, highlightbackground=BORDER,
                                highlightcolor=ACCENT)
        self.en_plug.pack(fill='x', padx=16, pady=4, ipady=6)
        tk.Label(inner, text="Pasang huruf berpasangan, contoh: AB CD EF\n(maks 13 pasang)",
                 font=self.f_small, bg=BG_CARD, fg=FG_MUTED,
                 justify='left').pack(anchor='w', padx=16, pady=(0,4))

        self._sec(inner, " Ringkasan Konfigurasi")
        self.en_summary = tk.Label(inner, text="—",
                                    font=font.Font(family="Courier New", size=10),
                                    bg=BG_CARD, fg=ACCENT2,
                                    justify='left', wraplength=300)
        self.en_summary.pack(anchor='w', padx=16, pady=(4,12))

        # Initialize visibility
        self._enigma_refresh_ui()

        kr = self._keyrow(p, 1, 3)
        self._btn(kr, "PROSES  (Enkripsi / Dekripsi)", self._enigma_proc,
                  ACCENT2, pad_x=20, pad_y=9).pack(side='left', padx=10)
        self._btn(kr, "Bersihkan",
                  lambda:(self.en_in.delete('1.0','end'),
                          self._settext(self.en_out,"")),
                  BORDER).pack(side='left', padx=4)
        self._btn(kr, "Update Ringkasan",
                  self._enigma_refresh_ui, GOLD).pack(side='left', padx=8)


    def _sec(self, parent, title):
        tk.Label(parent, text=title, font=self.f_lbl,
                 bg=BG_CARD, fg=GOLD, anchor='w').pack(fill='x', padx=16, pady=(14,2))
        tk.Frame(parent, bg=BORDER, height=1).pack(fill='x', padx=16, pady=(0,4))

    def _enigma_refresh_ui(self, *_):
        n = self.en_num.get()
        for i, row in enumerate(self.en_rotor_rows):
            if i < n: row.pack(fill='x', padx=16, pady=4)
            else:     row.pack_forget()
        try:
            rotors = [self.en_rotor_cbs[i].get() for i in range(n)]
            pos    = ''.join((self.en_rotor_pos[i].get()[:1].upper() or 'A') for i in range(n))
            plug   = self.en_plug.get().upper().strip() or '(kosong)'
            self.en_summary.config(
                text=f"Jumlah rotor : {n}\n"
                     f"Rotor        : {' – '.join(rotors)}\n"
                     f"Posisi awal  : {pos}\n"
                     f"Plugboard    : {plug}")
        except Exception:
            pass

    def _enigma_proc(self):
        try:
            n      = self.en_num.get()
            rotors = [self.en_rotor_cbs[i].get() for i in range(n)]
            pos    = ''.join((self.en_rotor_pos[i].get().strip().upper() or 'A')[0]
                             for i in range(n))
            if len(pos) != n or not pos.isalpha():
                raise ValueError(f"Posisi harus {n} huruf (satu per rotor)")
            plugs = self.en_plug.get().split()
            txt   = self.en_in.get('1.0','end').strip()
            if not txt: raise ValueError("Teks input kosong")
            machine = EnigmaMachine(rotors, list(pos), plugs)
            result  = machine.process(txt)
            self._settext(self.en_out, result)
            self._enigma_refresh_ui()
            self._status(f"Enigma OK — {n} rotor: {' – '.join(rotors)},  posisi: {pos}")
        except Exception as e:
            messagebox.showerror("Error", str(e))



if __name__ == "__main__":
    app = CryptoApp()
    app.mainloop()