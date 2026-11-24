def sat_to_number(s):
  s = s.split(' ')
  s = [int(x) for x in s]
  s = ['1' if x > 0 else '0' for x in s]
  s.reverse()
  return int('0b' + ''.join(s), base=2)

print(sat_to_number("2 -3 4 5 6 7 -8 -9 10 -11 12 -13 14 -15 -16 -17 -18 -19 -20 -21 -22 -23 -24 -25 -26 -27 -28 -29 -30 -31 -32 -33"))
print(sat_to_number("34 35 -36 -37 -38 -39 40 41 -42 -43 -44 -45 -46 47 -48 -49 -50 -51 -52 -53 -54 -55 -56 -57 -58 -59 -60 -61 -62 -63 -64 -65"))
