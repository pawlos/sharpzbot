## History of runs

> [!NOTE]
> Run are performed as a regular execution, nowhere near to be done in controlled environment; exact run values might not be repeatable

Running original code with no changes:

```
❯ dotnet run --configuration release
choice_type,choice,dice,rolls_remaining,upper_total,yahtzee_bonus_avail,open_slots,expected_value
ChoiceEV(31,254,58902)                                                                                         00:56:47 / 00:00:00
█████████████████████████████████████████████████████████████████████████████████████████████████████████████████████████████████
sharpzbot on  master [?] via .NET v9.0.101 🎯 net6.0 took 56m50s
```

Switching to .NET 9:

```
❯ dotnet run --configuration release
choice_type,choice,dice,rolls_remaining,upper_total,yahtzee_bonus_avail,open_slots,expected_value
ChoiceEV(31,254,58902)                                                                                         00:47:26 / 00:00:00
█████████████████████████████████████████████████████████████████████████████████████████████████████████████████████████████████
sharpzbot on  master [!?] via .NET v9.0.101 🎯 net9.0 took 47m28s
```