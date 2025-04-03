namespace Flexy
{
    public class FlexyDigest
    {
        private int StateWidthBits = 1600;
        private int StateWidthBytes;
        private int StateWidthUlongs;

        private int CapacityBits = 1024;
        private int RateBits;
        private int RateBytes;

        private int OutputLengthBits = 2048;
        private int OutputLengthBytes;

        private int Rounds = 24, ComputeRounds = 12;

        private readonly ulong[] RoundConstants = new ulong[]
        {
            0x0000000000000001UL, 0x0000000000008082UL, 0x800000000000808aUL,
            0x8000000080008000UL, 0x000000000000808bUL, 0x0000000080000001UL,
            0x8000000080008081UL, 0x8000000000008009UL, 0x000000000000008aUL,
            0x0000000000000088UL, 0x0000000080008009UL, 0x000000008000000aUL,
            0x000000008000808bUL, 0x800000000000008bUL, 0x8000000000008089UL,
            0x8000000000008003UL, 0x8000000000008002UL, 0x8000000000000080UL,
            0x000000000000800aUL, 0x800000008000000aUL, 0x8000000080008081UL,
            0x8000000000008080UL, 0x0000000080000001UL, 0x8000000080008008UL
        };

        private readonly int[,] RotationOffsets = new int[5, 5]
        {
            { 0, 36, 3, 41, 18 },
            { 1, 44, 10, 45, 2 },
            { 62, 6, 43, 15, 61 },
            { 28, 55, 25, 21, 56 },
            { 27, 20, 39, 8, 14 }
        };

        public FlexyDigest(int outputLengthBits = 2048, int capacityBits = 1024, int stateWidthBits = 1600, int computeRounds = 12)
        {
            OutputLengthBits = outputLengthBits;
            CapacityBits = capacityBits;
            StateWidthBits = stateWidthBits;
            ComputeRounds = computeRounds;

            StateWidthBytes = StateWidthBits / 8;
            StateWidthUlongs = StateWidthBytes / 8;

            RateBits = StateWidthBits - CapacityBits;
            RateBytes = RateBits / 8;

            OutputLengthBytes = OutputLengthBits / 8;
        }

        public byte[] ComputeHash(byte[] input)
        {
            byte[] theHash = input;

            for (int i = 0; i < ComputeRounds; i++)
            {
                ulong[] state = new ulong[StateWidthUlongs];
                int offset = 0;

                while (offset < theHash.Length)
                {
                    int bytesToProcess = Math.Min(RateBytes, theHash.Length - offset);
                    AbsorbBlock(state, theHash, offset, bytesToProcess);
                    offset += bytesToProcess;

                    if (bytesToProcess == RateBytes)
                    {
                        KeccakF1600(state);
                    }
                }

                byte[] paddedBlock = new byte[RateBytes];
                int lastBlockSize = theHash.Length % RateBytes;
                Buffer.BlockCopy(theHash, theHash.Length - lastBlockSize, paddedBlock, 0, lastBlockSize);

                paddedBlock[lastBlockSize] = 0x06;
                paddedBlock[RateBytes - 1] |= 0x80;

                AbsorbBlock(state, paddedBlock, 0, RateBytes);
                KeccakF1600(state);

                byte[] output = new byte[OutputLengthBytes];
                int outputGenerated = 0;
                while (outputGenerated < OutputLengthBytes)
                {
                    int bytesToSqueeze = Math.Min(RateBytes, OutputLengthBytes - outputGenerated);
                    SqueezeBlock(state, output, outputGenerated, bytesToSqueeze);
                    outputGenerated += bytesToSqueeze;

                    if (outputGenerated < OutputLengthBytes)
                    {
                        KeccakF1600(state);
                    }
                }

                theHash = output;
            }

            return theHash;
        }

        private void AbsorbBlock(ulong[] state, byte[] block, int offset, int count)
        {
            for (int i = 0; i < count; ++i)
            {
                int stateIndex = i / 8;
                int byteShift = (i % 8) * 8;
                state[stateIndex] ^= (ulong)block[offset + i] << byteShift;
            }
        }

        private void SqueezeBlock(ulong[] state, byte[] output, int offset, int count)
        {
            for (int i = 0; i < count; ++i)
            {
                int stateIndex = i / 8;
                int byteShift = (i % 8) * 8;
                output[offset + i] = (byte)(state[stateIndex] >> byteShift);
            }
        }

        private void KeccakF1600(ulong[] state)
        {
            ulong[,] A = new ulong[5, 5];
            ulong[] C = new ulong[5];
            ulong[] D = new ulong[5];
            ulong temp;

            for (int y = 0; y < 5; y++)
            {
                for (int x = 0; x < 5; x++)
                {
                    A[x, y] = state[x + 5 * y];
                }

            }

            for (int round = 0; round < Rounds; round++)
            {
                for (int x = 0; x < 5; x++)
                {
                    C[x] = A[x, 0] ^ A[x, 1] ^ A[x, 2] ^ A[x, 3] ^ A[x, 4];
                }

                for (int x = 0; x < 5; x++)
                {
                    D[x] = C[(x + 4) % 5] ^ RotateLeft64(C[(x + 1) % 5], 1);
                }

                for (int y = 0; y < 5; y++)
                {
                    for (int x = 0; x < 5; x++)
                    {
                        A[x, y] ^= D[x];
                    }
                }

                ulong current = A[1, 0];

                for (int x = 0; x < 5; x++)
                {
                    for (int y = 0; y < 5; y++)
                    {
                        int nextX = y;
                        int nextY = (2 * x + 3 * y) % 5;
                        temp = A[nextX, nextY];
                        A[nextX, nextY] = RotateLeft64(current, RotationOffsets[x, y]);
                        current = temp;
                    }
                }

                for (int y = 0; y < 5; y++)
                {
                    ulong[] T = new ulong[5];

                    for (int x = 0; x < 5; x++)
                    {
                        T[x] = A[x, y];
                    }

                    for (int x = 0; x < 5; x++)
                    {
                        A[x, y] = T[x] ^ ((~T[(x + 1) % 5]) & T[(x + 2) % 5]);
                    }
                }

                A[0, 0] ^= RoundConstants[round];
            }

            for (int y = 0; y < 5; y++)
            {
                for (int x = 0; x < 5; x++)
                {
                    state[x + 5 * y] = A[x, y];
                }
            }
        }

        private ulong RotateLeft64(ulong value, int count)
        {
            count %= 64;
            return (value << count) | (value >> (64 - count));
        }
    }
}