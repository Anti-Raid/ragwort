-- Run with luau -O2 luau_table_bench.luau and luau -O2 --codegen luau_table_bench.luau.
local iterations = 5000000
local rounds = 9

local function field3(n, t)
    local sum = 0
    for _ = 1, n do
        sum += t.id + t["author-id"] + t["channel-id"]
    end
    return sum
end

local function local3(n, t)
    local a, b, c = t.id, t["author-id"], t["channel-id"]
    local sum = 0
    for _ = 1, n do
        sum += a + b + c
    end
    return sum
end

local function field1(n, t)
    local sum = 0
    for _ = 1, n do
        sum += t.id
    end
    return sum
end

local function local1(n, t)
    local id = t.id
    local sum = 0
    for _ = 1, n do
        sum += id
    end
    return sum
end

-- Six fields and the same three keys as the Ragwort table_bench literal.
local record = { id = 1, content = 2, ["author-id"] = 3, ["channel-id"] = 4, ["guild-id"] = 5, pinned = 6 }
local cases = {
    { "field3", field3, 8 },
    { "local3", local3, 8 },
    { "field1", field1, 1 },
    { "local1", local1, 1 },
}
local results = {}
for _, case in cases do
    assert(case[2](100000, record) == 100000 * case[3])
    results[case[1]] = {}
end

for round = 1, rounds do
    for offset = 0, #cases - 1 do
        local case = cases[(round + offset - 1) % #cases + 1]
        local name, run, expected = case[1], case[2], case[3] * iterations
        local start = os.clock()
        local sum = run(iterations, record)
        local elapsed = os.clock() - start
        assert(sum == expected)
        results[name][round] = elapsed * 1e9 / iterations
    end
end

local function report(name, samples)
    local sorted = table.clone(samples)
    table.sort(sorted)
    print(string.format("%-24s median %.3f  min %.3f  max %.3f", name, sorted[(rounds + 1) / 2], sorted[1], sorted[rounds]))
end

print("Raw loops in ns/iteration. Paired differences in ns/read.")
for _, case in cases do
    report(case[1], results[case[1]])
end
for _, k in {1, 3} do
    local delta = {}
    for i = 1, rounds do
        delta[i] = (results["field" .. k][i] - results["local" .. k][i]) / k
    end
    report("extra per read (" .. k .. ")", delta)
end
