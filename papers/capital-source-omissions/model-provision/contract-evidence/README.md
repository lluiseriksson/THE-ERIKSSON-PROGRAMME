# Reading economic terms in a model-provision graph

A directed relation recording that one firm supplies a model to another does not identify who pays whom, for what, or how much. An analyst estimating provider revenue from this graph would need the contract date, the purchased service, the contractual payer and payee, and a distinction between commitments and payments. These are illustrated by six deliberately selected cases. They do not establish the frequency of any arrangement.

## Sample and reproducibility

We used the public [Cen et al. study](https://arxiv.org/html/2611.24927v1) and its [pinned underlying data](https://huggingface.co/datasets/sarahcen/ai-supply-chain/tree/e737b94a38cf77b2ec3a29cb1c6bd756fb1329fb). The original category includes access, licensing and hosting. This appendix tests a potential economic interpretation of the graph. The original extraction makes a broader claim about provision.

The protocol selects from dated, directed, established model-provision records with a company recipient, November 2022 through October 2026 inclusive. Eighteen previously checked document dates are included by URL digest. We exclude the anthropic.com host, retain separate normalized recipient labels and rank common recipients first by the lower of their two distinct hostname counts, then by their sum, then alphabetically. There were 37 shared labels. A hostname count measures documentary coverage and may include dependent sources. The top three were selected before checking commercial terms.

| Recipient label | Hosts supporting Anthropic | Hosts supporting OpenAI |
|---|---:|---:|
| Microsoft | 18 | 33 |
| Snowflake | 8 | 4 |
| Salesforce | 7 | 4 |

The six pair-specific readings, including dates, party statements and comparison to URLs actually supporting the selected graph edges, are in [the ledger](source-ledger.json). Of the eight official announcements used there, two exactly match URLs supporting the corresponding pair in this slice. Six were additional primary sources. An additional source can corroborate a relationship or update its terms. It is not evidence about the wording of a sampled article.

## Two errors that change the economic interpretation

**Reversing a model-supply edge to infer a revenue share can give the wrong direction.** Microsoft retained an OpenAI licence in April 2026. From that amendment, the revenue-sharing clause pays Microsoft from OpenAI. The amendment ended the revenue share previously payable by Microsoft. In January 2025, Microsoft had described a two-way share. The underlying provider and recipient names stay the same across these contractual regimes. The comparison identifies the direction for this named clause only. Other contracts and net cash flows remain outside it. [Earlier terms](https://blogs.microsoft.com/blog/2025/01/21/microsoft-and-openai-evolve-partnership-to-drive-the-next-phase-of-ai/) · [Amendment](https://blogs.microsoft.com/blog/2026/04/27/the-next-phase-of-the-microsoft-openai-partnership/)

**A correctly transcribed dollar amount can still be assigned to the wrong service.** In the announcement covering Claude on Microsoft products, Anthropic committed $30 billion to buy Azure computing capacity. The same announcement separately describes Microsoft's investment commitment. Crediting either to Microsoft's purchases of Claude would misidentify the economic object. [Joint announcement](https://blogs.microsoft.com/blog/2025/11/18/microsoft-nvidia-and-anthropic-announce-strategic-partnerships/)

Snowflake announced two separate $200 million partnerships. There is primary evidence for purchase commitments beyond the headlines. Snowflake's SEC filing describes an unnamed AI provider under a three-year deal starting December 2025 with minimum annual spending of $50 million, $70 million and $80 million. Eligible use through certain clouds could count. A later filing puts the amended minimum at $390 million, of which $270 million remained at 31 July 2026. A match on dates and amounts is compatible with the named Anthropic announcement. The two filing passages leave the counterparty unnamed, so this audit keeps that linkage unresolved. Subtracting the remaining commitment from the total does not by itself identify a cash receipt by any named firm. [Original filed note](https://www.sec.gov/Archives/edgar/data/1640147/000164014725000211/R19.htm) · [Amended commitment](https://www.sec.gov/Archives/edgar/data/1640147/000164014726000037/snow-20260731.htm)

For Salesforce, the releases explicitly distinguish model availability, platforms and customers. Claude via Amazon Bedrock in Agentforce gives a concrete multilateral delivery route. The reported deployment identifies the hosting intermediary but leaves the invoice route open. [Salesforce–Anthropic](https://investor.salesforce.com/news/news-details/2025/Anthropic-and-Salesforce-Expand-Strategic-Partnership-to-Deliver-Trusted-AI-for-Regulated-Industries/default.aspx) · [Salesforce–OpenAI](https://www.salesforce.com/news/press-releases/2025/10/14/openai-partnership-expansion-announcement/)

## Verification and scope

The exact sample-selection script ran on a dedicated Colab Linux session against the Parquet SHA-256 `89752ca13ef5516cf22805616a5976b0fecc717c4fecb29e739bc7297385f56a`. Its private archive SHA-256 was `45d885514c31c915760d52eecc865fc44ef92b1b2f9a03f0fa4668bdc7395b5c`. The accompanying [rank file](shared-rank.json) contains label-level counts. The source comparisons are documentary analysis and have not received independent review. Selection favors well-documented labels and does not support a prevalence estimate, a corrected revenue ranking or a conclusion about unreported payments.
