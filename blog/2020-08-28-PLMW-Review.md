---
title: A Review of PLMW at ICFP 2020
author: Lawrence Dunn
tags: review, conferences
description: A review of the Programming Languages Mentoring Workshop at ICFP
withtoc: true
---

The [Programming Languages Mentoring Workshop](https://www.sigplan.org/Conferences/PLMW/) (PLMW) is a one-day workshop hosted at [SIGPLAN](https://www.sigplan.org/)-affiliated conferences including [POPL](https://sigplan.org/Conferences/POPL/), [PLDI](https://sigplan.org/Conferences/PLDI/), [SPLASH](https://sigplan.org/Conferences/SPLASH/), and [ICFP](https://sigplan.org/Conferences/ICFP/). Since 2012 the workshop has helped participants, primarily late undergraduates and early graduate students, explore careers in programming language research in industry and academia. I attended PLMW for the first time at [ICFP 2020](https://icfp20.sigplan.org/) as a PhD student entering my third year. In this post I'll talk about my experience.

## Conferences and Workshops
I'd like to start with a quick rundown of how academic conferences are organized, since I once found this confusing and imagine others do too. A large conference like ICFP is a complex thing, as you can see from the [program](https://icfp20.sigplan.org/program/program-icfp-2020?). The main unit of organization is a *session,* which often consists of a few speakers giving talks one after another. *Poster sessions* are a dedicated time for the audience to walk around and look at posters highlighting projects attendees are working on. Multiple sessions can occur simultaneously in different rooms, although *plenary* sessions are attended by everyone. Similarly to other large conferences, ICFP has a "core" conference which lasts a few days, but it also acts as a host for *co-located events* where interest groups can organize their own events under the larger ICFP umbrella. These events can take the form of *workshops*, which are essentially small sub-conferences that can potentially have their own fees or application process, or *tutorials*, with a presenter demonstrating how to achieve some practical goal with a specific tool. At ICFP 2020, there were dedicated workshops for the programming languages OCaml, Haskell, and Erlang, among other things. (Technically the Haskell event was a two-day *symposium*, which means something like "large workshop" or "small conference.")

As the name suggests, PLMW is a workshop that you must apply to, although admittance into the workshop typically includes automatic registration for the hosting conference. At ICFP 2020, the workshop was hosted on the Sunday before the main ICFP events that began Monday. Besides being useful in its own right, the workshop was also a gentle introduction to a weeklong conference that was likely the first PL conference for many of its attendees.

## Why PLMW exists
Students interested in PL often have many questions about the field. Here's a few I've personally asked at some point:

- What exactly is it? Is it right for me?
- How do I get a degree in it?
- How can I be *competitive* for it?
- What are some problems to work on?
- Where do I find a research supervisor?
- What's impredicative polymorphism? [^1]

[^1]: You can substitute any technical question you like here. For the record, impredicative polymorphism is the kind of polymorphism found in languages like [Coq](https://coq.inria.fr/). If you like functional programming, you might be more familiar with prenex polymorphism, a restricted kind of polymorphism which is better for type inference.

I'm sure you can think of more.

It can be challenging to find answers to these sorts of questions, since programming language research can be a niche topic. Many institutions have few researchers in the field, if any, and they often lack a dedicated course in the subject. Undergraduates have difficulty finding research advisors for senior projects or writing grad school applications. It does not help matters that PL research commonly attracts students without computer science backgrounds, particularly math students (hello). The field is also rife with impenetrable jargon as embodied by the famous quip, "A monad is just a monoid in the category of endofunctors, what's the problem?" Jobs in the field are few in number and typically quite competitive. On top of all of this, students from disadvantaged or underrepresented backgrounds face their own set of challenges entirely.

These factors can cause a gap between the PL research community and potential new practitioners. PLMW exists to help bridge this gap. Each year there are about four opportunities to attend a SIGPLAN conference that hosts the workshop. As I said, students must apply to the program before the conference (so be vigilant about those deadlines). Admitted students can have the cost of conference registration covered, as well as travel fees. Many students attend the program several times. [^2]

[^2]: The financial awards are generally only given out once per student, but it is likely that attendees of this virtual PLMW will be able to apply again for funding to attend a physical PLMW.


# My experience

As I was applying to the program, I wasn't sure whether PLMW was right for me as a third-year student already working on research under two advisors. Was I already too far in my career for a mentoring workshop? Likewise I imagine some students feel the opposite way: Am I ready to attend an academic conference in a subject I'm not very familiar with? But my application was accepted, and I soon learned that other participants were from a variety of backgrounds and levels of experience. I now think virtually any student considering a career working on programming languages should consider PLMW.

I should note at this point that ICFP 2020, like many other conferences this year, was hosted virtually on [Clowdr](https://www.clowdr.org/). Clowdr was created as a highly cost-effective platform for academic virtual conferences, and it does an admirable job mimicking the atmosphere of a physical conference. In particular, it allows for the chance meetings and ad-hoc conversations with fellow enthusiasts that physical conferences facilitate. This is important to note because, as I will discuss, these aspects are some of the most valuable parts of attending a conference.

On the morning of PLMW, in a virtual chatroom, I and other conference-goers exchanged introductions in a "Mentoring" channel designed to connect short- and long-term mentors with students. As a third-year PhD student, I was in the interesting position of being experienced enough to give advice to earlier students but new enough to get some highly useful advice from working researchers. After I introduced myself, one student contacted me to ask how I found my current research topic. The problem of finding a good research problem is something I never quite understood myself, so I was happy to describe the long and sometimes confused story of how I ended up working on my current work.

Later I had the good fortune to notice that another student was a good fit for the [Frost Scholarship](https://www.scholarshipdesk.com/frost-scholarship-programme-florida-at-oxford-university/), a wonderful program that is not as well-known as comparable ones. I mostly know about the award because I happen to be among the first students to receive it, so I introduced myself more personally and described the nature of the award and its merits. It is precisely these kinds of chance encounters that make conferences so valuable. In fact, when I later asked an unrelated question to [Simon Peyton Jones](https://www.microsoft.com/en-us/research/people/simonpj/), he emphasized that the course of an academic career is highly non-deterministic and easily affected by random incidents such as the one just described. The takeaway is this: In an academic (or related) career, you simply cannot know in advance which moments will most affect your overall trajectory. So take every opportunity you can get, keep an open mind, and meet people! This is part of what PLMW is for.

## The presentations

The workshop featured several talks, some emphasizing technical topics, others focusing on more general career advice.

The day kicked off with [Derek Dreyer](https://people.mpi-sws.org/~dreyer/) teaching us how to write a readable paper. Many in the audience agreed that a non-trivial fraction of research papers are hard to read simply because they are not written well. I found this talk exciting because several weeks ago, by coincidence, a reading group at Penn read part of Dreyer's PhD dissertation and agreed that it was a good example of clear writing. Hearing directly from researchers whose work you admire is an exciting, but sometimes intimidating, part of the conference experience.

After a half-hour break spent socializing, we had a session of three 40-minute talks. Two of the presentations were technical, focusing on constraints solvers and operational semantics. They covered material I mostly understood already, but they were enjoyable nonetheless. I would have found it useful to attend many years ago, particularly to learn about operational semantics. Instead, I was able to offer some advice to newer students, namely that the subtlety of the topic is hard to appreciate until you start trying to prove theorems about real languages. I think most students would have found the talks useful, even without much background in the respective subjects, if only to get some exposure to the basic ideas.

The talk I was most interested in was titled "Managing your Research, your Advisor, your PhD." The main idea was that completing a PhD is a responsibility falling largely on *your* shoulders and not your advisor's. *You* must be the one to balance your time, keep track of your research projects, initiate meetings (sometimes), and generally dedicate yourself to furthering your education. Students should therefore try to learn and apply these skills as soon as possible. This requires advice and practice, so I was grateful for the talk.

Following the session was a social time that doubled as a lunch break. After that, we had another session of two 45-minute talks.

First, [Kenny Foner](https://very.science/) gave a presentation titled, "How Can I Academia When My Brain Can't Even? Mental Health in Grad School and Beyond." My impression was that this talk generated the most discussion and excitement at PLMW this year. I'm not sure how well I can capture the emotional impact of the talk, but fortunately Kenny has given it many times and a video from POPL is available [here on Youtube](https://www.youtube.com/watch?v=Mi2dMiGSu_4). The message, in short, is as follows: Doing a PhD is very stressful, and many academics will experience at least some symptoms of depression or anxiety in the course of their careers. Your mental health is something to take seriously, and all of us should understand the resources available to us, as well as resist internalizing or propagating the stigmas that can surround this topic. When things feel overwhelming, don't hesitate to take some time off or seek help.

The second talk by [Nada Amin](https://namin.seas.harvard.edu/people/nada-amin) explained an interesting use of functional programming to explore graph-based databases, which evidently is useful for biomedical research. Of all of the talks, this was the one I benefited from most on a technical level. The talk presented many ideas and technical terms that I want to explore further, as applying PL theory to data management is a topic I find compelling. As I look more into the research presented, I would not be surprised to find some inspiration for my own research on [Datalog](https://en.wikipedia.org/wiki/Datalog).

To finish the workshop, our final session was a panel discussion with a variety of researchers drawn from industry and academia. It was only scheduled for an hour, but a few panelists stayed much longer to answer questions from an eager audience. Students earlier in their careers asked how to be choose a graduate school, how to find a job, and how to write good applications, among other things. Later students asked questions about the publication process, knowing if a research area is going to produce novel results, and how to decide between careers in industry and academia. A fun time was had by all.

# Conclusion

PLMW 2020 was a fantastic experience that I would recommend to anyone. The organizers did a great job, and the atmosphere was at all times respectful, encouraging, and engaging. Attendees benefited to hear from real experts in their fields, as well as other students at different points in their careers. To the greatest extent possible, Clowdr did a commendable job creating the illusion of a physical conference with all its random encounters with other students and researchers. The talks and the speakers were diverse and well-selected in several respects, presenting a good picture of what the PL community is like. I think every student walked away from PLMW 2020 with a greater understanding and excitement for programming language research. I know I did.
