# Preregistration: four-cell pair mean-value batch

Register, before reading results, the four adjacent beta cells

```text
[13059/128,13060/128]
[13060/128,13061/128]
[13061/128,13062/128]
[13062/128,13063/128]
```

Use `lambda=[3/2,19/10]`, 115 modes, beta/lambda Taylor orders 50/50, and
500 Arb bits.  The existing ordered runner may use two workers and must emit
production plus replay for every cell.  A green cell is one candidate only;
any timeout or nonnegative upper endpoint is retained as a diagnostic.  No
G2/G6 promotion is authorized by this batch.
