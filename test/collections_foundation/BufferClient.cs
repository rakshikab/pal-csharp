using PalLang;

/// <summary>
/// R22.1. A client of a declared indexer: <c>b[i]</c> reads through <c>get_Item</c> and
/// <c>b[i] = v</c> writes through <c>set_Item</c>, as R9.20a's property read is its
/// getter. Neither is R20.4's array access, which a class receiver does not type-check as.
/// </summary>
public static class BufferClient
{
    [Ensures("Result == 30")]
    public static int SumFirstTwo()
    {
        var b = new Buffer<int>();
        b.Add(10);
        b.Add(20);
        return b[0] + b[1];
    }

    [Ensures("Result == 99")]
    public static int OverwriteFirst()
    {
        var b = new Buffer<int>();
        b.Add(10);
        b[0] = 99;
        return b[0];
    }
}
