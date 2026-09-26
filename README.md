# 储能环联锁 LTL 放行时序复核服务

从**指定初态**出发，判定规程的**每一条无限执行**是否都满足放行时序公式（LTL
全称路径模型检测）。**不**以有限回放掩盖迟发或永不发生：检测基于否定公式的
广义 Büchi 自动机 × 规程乘积上的可达接受环，结论为完整判定（非采样、无深度截断）。

## 判定算法（无回放深度 / 无随机采样 / 不只看状态标签）

1. **规范化**：将公式 φ 转为否定正规式 NNF(¬φ)，否定下压，F/G、U/V 互为对偶。
2. **否定公式的广义 Büchi 自动机（GBA）**：取 NNF(¬φ) 的 Fischer–Ladkin
   闭包（子式 + 不动点时序式的 `X` 迁移式，拓扑排序），用 tableau 规则把
   局部一致的「基本公式集」作为自动机状态；每个 `F`/`U` 事件性子式对应一个
   **公平集**。自动机**按需展开（on-the-fly）**，只生成乘积中真正可达且与
   位置标签相容的状态，不预枚举 `2^闭包`、不建 `|A|²` 迁移表（24 位置复杂
   公式实测毫秒级）。
3. **与规程乘积**：状态 = 位置 × GBA 基本集；沿调用方声明的有向切换迁移，
   标签须与自动机状态的字面量一致。`X` 后继约束与标签冲突时该迁移无后继。
4. **可达接受环**：对可达乘积图跑 Tarjan SCC，存在被**全部**公平集无限次
   命中的非平凡 SCC 当且仅当存在 ¬φ 的无限执行（φ 被违反）；在 SCC 内拼出
   一条**前缀 + 重复闭环**的套索，并独立重放验证每一步切换真实存在且闭环闭合。
5. **证据**：在套索周期序列上以嵌套 μ/ν 不动点（F/U 最小不动点、G/V 最大
   不动点）计算 φ **全部子式在每个位置的真值**。

该核心经约 **1.2 万个随机小模型的独立预言机差分模糊测试**（预言机与本
tableau 完全独立：直接枚举位置图上的简单前缀+闭环行走，按周期语义求值），
零分歧；另加约 2.6 千个多公平集专项用例。

## 目录

```
app/ltl_parser.py   LTL 词法/语法解析、AST、子式索引
app/checker.py      NNF 规范化、按需 GBA、乘积、SCC、套索、子式真值证据
app/suppression.py  最小切换抑制审计：分支定界求全局最少禁用切换
app/validation.py   结构/公式校验（定位拒绝，非法不生成审计）
app/storage.py      审计编号持久化（JSON，原子写，线程安全）
app/server.py       零第三方依赖的 HTTP 服务（标准库）
app/healthcheck.py  容器健康检查脚本
scripts/verify.py   Compose verify：构建检查 + 单元测试 + HTTP 冒烟
tests/              49 个 unittest 用例
examples/           合规与违规（永不放行闭环）两个示例
Dockerfile          python:3.11-slim，零 pip 依赖，带 HEALTHCHECK
docker-compose.yml  ltl 服务 + verify 验收服务
```

## 请求字段（2–24 个唯一位置）

| 字段 | 说明 |
|---|---|
| `locations` | 2..24 个唯一位置，合法标识符 |
| `switches` | 有向切换，`id` 全局唯一，`source`/`target` 必须指向已声明位置 |
| `initial` | 初态，必须是已声明位置 |
| `propositions` | **每个**位置一个数组，列出该位置成立的原子命题（公式只能用这些命题） |
| `formula` | 仅含声明命题、`! & | X F G U` 与括号；二元 `U` 须写成 `(a U b)` |

> 注意：原子命题名不能以大写 `F/G/X/U` 开头（否则与算子词法冲突），
> 也不能用 `true`/`false` 等保留字；每个位置至少有一条外出切换。
> 命题是「闭世界」：未列出即不成立。
>
> 语法不含蕴含 `->`。联锁中常见的「请求必终将放行」`G(request → F granted)`
> 写作 `G(!request | F granted)`。

## HTTP 接口

| 方法 | 路径 | 说明 |
|---|---|---|
| `POST` | `/checks` | 提交复核；成功返回 201 并分配编号，非法输入返回 400 且**不**生成审计 |
| `GET`  | `/checks/<id>` | 按编号读取：成立结论，或带每步位置/切换/子式真值的违规套索 |
| `POST` | `/checks/<id>/suppressions` | 对已判**不成立**的复核发起最小切换抑制审计；成功 201 并分配审计编号 |
| `GET`  | `/suppressions/<id>` | 按审计编号读取抑制审计（刷新/重启后仍可读） |
| `GET`  | `/health` | 健康检查 |

合规结果：`{"id","formula","initial","spec","holds":true,"normalization":{
"negation_nnf", "method"}, "stats":{...}}`；其中 `spec` 为保存的规程
（位置/切换/命题/公式），供抑制审计重构乘积，保存后不被改写。

违规结果额外含 `violation`：`prefix_length`、`cycle_length`、
`loop_start_index`、`steps[]`（每步 `location`、`switch_taken`、
`propositions`、`subformula_truth`、`formula_true_here`、
`negation_automaton_formulas`）与说明 `note`。

## 最小切换抑制审计

安全工程师在已读取到**不成立**结论的复核上，可发起最小切换抑制审计：
确认至少临时禁用哪些既有有向切换，才能使**同一初态**起的所有无限执行
都满足原公式。原复核与规程不被改写。

1. **重构**：从来源复核保存的规程与公式重新构造否定 GBA 乘积。
2. **套索 → 冲突集**：每次发现的可达接受套索，其全部切换（前缀 + 闭环）
   构成必须命中的切换集合 —— 任何可行禁用集都至少含其一，否则该套索在
   禁用后的规程中仍然存活。
3. **分支定界**：持续向候选禁用集加入套索内切换并重跑完整复核，求得
   **全局最少**集合；候选集不得令任一位置失去全部外出切换；同样大小的
   可行修复按切换标识升序序列取字典序最小（稳定裁决）。
4. 不使用有限回放、随机搜索、逐条贪心禁用，也不只修补首次证据。

成功审计（201，`SUP-000001` 起编号）保存：来源复核编号
（`source_check_id`）、原公式摘要（`formula_summary`）、最少数量
（`min_disabled_count`）、禁用切换（`disabled_switches`，升序）、
修复后结论（`post_repair`）与可复算的最终证明（`proof`：禁用后规程
`reduced_procedure` + 重跑复核的 `final_check`，重新提交即可复算同一
成立结论）。审计落盘持久化，刷新或服务重启后按审计编号仍可读取。

失败定位（均**不**创建审计）：

- `404` 来源复核编号不存在；
- `409 source_already_holds` 来源结论本就成立；
- `422 no_feasible_suppression` 不存在保持全部位置可外出的修复。

## 运行

```bash
# 启动服务（默认 8080；端口可调）
LTL_HOST_PORT=9090 docker compose up -d --build ltl

# 提交合规/违规示例
curl -s -X POST localhost:9090/checks -H 'Content-Type: application/json' \
  --data @examples/compliant.json
curl -s -X POST localhost:9090/checks -H 'Content-Type: application/json' \
  --data @examples/violation.json

# 按编号读取
curl -s localhost:9090/checks/CHK-000001

# 对不成立的复核发起最小切换抑制审计，并按审计编号读取
curl -s -X POST localhost:9090/checks/CHK-000002/suppressions
curl -s localhost:9090/suppressions/SUP-000001

# 验收（构建检查 + 49 单测 + HTTP 冒烟：永不放行违规闭环、两条替代违规环的
# 最小切换抑制修复与原有读取回归），退出码报告
docker compose up --build verify
# 自定义端口：
LTL_PORT=8090 LTL_HOST_PORT=9090 docker compose up --build verify
```

## 拒绝情形（定位、不生成审计编号）

- 位置数不在 2..24、位置/切换 id 重复、初态悬空；
- 切换端点悬空（指向未声明位置）；
- 任一位置无外出切换（死端）；
- 缺少某位置的命题声明、命题名非法/重复/与算子保留字冲突；
- 公式含未声明命题、非法字符、括号错配、运算符缺操作数、括号外裸 `U` 等。

错误形如：`{"error":"validation_failed","errors":["位置 'b' 没有外出切换（死端，禁止）", ...]}`。

## 本地开发（无需 Docker）

```bash
python3 -m unittest discover -s tests -v
LTL_PORT=8080 LTL_DATA_DIR=./data python3 -m app.server
LTL_BASE_URL=http://127.0.0.1:8080 python3 scripts/verify.py
```
