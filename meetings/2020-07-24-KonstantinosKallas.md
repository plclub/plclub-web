---
title: "Serverless Workflows with Azure Durable Functions"
speaker: "Konstantinos Kallas"
semester: "SP20"
---

Abstract: Developing serverless applications on the cloud involves several reliability and complexity challenges, mostly because the main computation component is stateless functions that are not guaranteed to execute reliably. To achieve reliability, developers have to compose these functions with a variety of external services; functions pass their results among them using reliable queues, and functions use storage to save and retrieve their state. In this presentation, I will be talking about Durable Functions, a programming model that allows implementing complex workflows with simple <choose-the-language-of-your-preference> code. I will give examples of the programming model as well as describe its implementation and how it achieves reliable execution.

For anyone who watched the PLDI talk that we gave with Sebastian and David, there will be some additional material regarding the Durable Functions implementation and about the optimizations that we have implemented.

Homework:
- If you are not familiar with serverless computing, I would suggest taking a brief look at the first two chapters of the Berkeley report on serverless computing: https://www2.eecs.berkeley.edu/Pubs/TechRpts/2019/EECS-2019-3.pdf. Feel free to read more than just the first two chapters (or less if you don't have time).
- If you are already familiar with serverless computing, you could take a look at an overview of Durable Functions aimed for developers: https://docs.microsoft.com/en-us/azure/azure-functions/durable/durable-functions-overview?tabs=csharp.

See you tomorrow :)

Konstantinos
