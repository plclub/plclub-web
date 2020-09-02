---
title: A Review of PLMW at ICFP 2020
author: Lawrence Dunn
tags: review, conferences
description: A review of the Programming Languages Mentoring Workshop at ICFP 2020
withtoc: true
---

The [Programming Languages Mentoring Workshop](https://www.sigplan.org/Conferences/PLMW/) (PLMW) is a one-day workshop hosted at [SIGPLAN](https://www.sigplan.org/)-affiliated conferences including [POPL](https://sigplan.org/Conferences/POPL/), [PLDI](https://sigplan.org/Conferences/PLDI/), [SPLASH](https://sigplan.org/Conferences/SPLASH/), and [ICFP](https://sigplan.org/Conferences/ICFP/). Since 2012 the workshop has helped participants, primarily senior undergraduates and early graduate students, explore careers in programming language research in industry and academia. I attended PLMW for the first time at [ICFP 2020](https://icfp20.sigplan.org/) as a PhD student entering my third year. In this post I'll talk about my experience. Along the way, since I imagine many readers are not seasoned conference-goers, I'll offer some tips about navigating computer science conferences so you know what to expect walking into something like PLMW.

By the way, I should note that ICFP 2020 was hosted virtually on [CLOWDR](https://www.clowdr.org/), a recently-created open source virtual conferencing platform. Virtual conferencing is pretty new to most of us, and CLOWDR is newer still, so I'll talk a little bit about the virtual aspect of ICFP as well.

## What are workshops?
I admit, there was a time when a "workshop" to me meant someone's garage. If you're in the same boat, you might have some questions about how this whole thing works. Otherwise you can skip this section and proceed straight into the review.

A large conference like ICFP is a complex thing (just take a look at [the program](https://icfp20.sigplan.org/program/program-icfp-2020?)), and if you don't know the terminology it's easy to feel disoriented. In my experience the complexity of these sorts of things contributes to the inaccessibility of the CS community, and I want to start off by making sure readers at least have some understanding of how conferences and workshops are laid out.

The main unit of conference organization is a *session*, and there can be several sessions occurring simultaneously. Usually a session consists of a few speakers giving talks one after another, although some varieties exist:

Poster sessions
: A dedicated time to look at posters and talk to their authors

Plenary sessions
: Large talks attended by everybody

Tutorials
: Sessions where a presenter describes how to achieve a goal with a specific tool

But a conference like ICFP is not just a set of sessions. Like many other large conferences, ICFP has a "core" conference which lasts a few days, but it also acts as a host for *co-located events* for interest groups to organize their own programs under the larger ICFP umbrella. Often such events take the form of *workshops*, which are essentially small subconferences. In general, a workshop can have its own application process, accept its own papers, or have its own fees, etc. At ICFP 2020 there were workshops for the programming languages OCaml, Haskell, and Erlang, among other things. (Technically the Haskell event was a two-day *symposium*, which means something like "large workshop" or "small conference.")

As the name suggests, PLMW is a workshop which is co-located with larger SIGPLAN conferences ([SIGPLAN](https://www.sigplan.org/) being the programming languages division of the [ACM](https://www.acm.org/), which is an international association for professionals in computation). You have to apply to it, but admittance into the workshop typically includes automatic registration for the hosting conference. At ICFP 2020, the workshop was hosted on the Sunday before the main ICFP events that began Monday. The workshop itself is organized as a set of speaker sessions with time in between for socializing.

## What is PLMW for?
Students interested in programming language research (colloquially, just "PL") often have many questions about the field. Here's a few I've personally asked at some point:

- What exactly is it? Is it right for me?
- How can I be competitive for PL-related jobs and graduate programs?
- What are some problems to work on?
- Where do I find a research supervisor?
- What's impredicative polymorphism? [^1]

[^1]: You can substitute any technical question you like here. For the record, impredicative polymorphism is the kind of polymorphism found in languages like [Coq](https://coq.inria.fr/). If you like functional programming, you might be more familiar with prenex polymorphism, a restricted kind of polymorphism which is better for type inference.

I'm sure you can think of more.

It can be challenging to find answers to these sorts of questions because PL research can be a niche topic most commonly associated with graduate-level studies. Many institutions have few researchers in the field, if any, and they often lack dedicated courses in the subject. Undergraduates have difficulty finding research advisors for senior projects or writing grad school applications, and it does not help matters that PL research often attracts students without computer science backgrounds (particularly math students like me). The field is also rife with impenetrable jargon as embodied by the famous quip, "A monad is just a monoid in the category of endofunctors, what's the problem?"[^2] Jobs in the field are few in number and typically quite competitive. On top of all of this, students from disadvantaged or underrepresented backgrounds face their own set of challenges entirely.

[^2]: See [here on StackOverflow](https://stackoverflow.com/questions/3870088/a-monad-is-just-a-monoid-in-the-category-of-endofunctors-whats-the-problem) for more info.

These factors can create a gap between the PL research community and potential new practitioners. PLMW exists to help bridge this gap. Each year there are about four opportunities to attend a SIGPLAN conference that hosts the workshop. As I said, students must apply to the program before the conference (so be vigilant about those deadlines). Admitted students can have the cost of conference registration covered, as well as travel fees. Many students attend the program several times. [^3]

[^3]: The financial awards are generally only given out once per student, but it is likely that attendees of this virtual PLMW will be able to apply again for funding to attend a physical PLMW.


# My experience

As I was applying to the program, I wasn't sure whether PLMW was right for me as a third-year student already working on research under two advisors. Was I already too far in my career for a mentoring workshop? Likewise I imagine some students feel the opposite way: Am I ready to attend an academic conference in a subject I'm not very familiar with? But my application was accepted, and I soon learned that other participants were from a variety of backgrounds and levels of experience. In retrospect, I would say any student seriously considering a career working on programming languages should consider PLMW.


The week before ICFP began we were sent a link to register on CLOWDR. The platform revolves around the metaphor of attending a physical conference and does an admirable job of this. When you first log in, you're in the "Lobby" and can chat virtually with other people there. You can also see which sessions are in progress and join in. Sessions for PLMW were held in [Zoom](https://zoom.us/), with CLOWDR orchestrating this and providing the right hyperlinks to join the current session.

On the morning of the workshop, in a virtual chatroom, I and other conference-goers exchanged introductions in a "Mentoring" channel designed to connect short- and long-term mentors with students. As a third-year PhD student, I was in the interesting position of being experienced enough to give advice to earlier students but new enough to get some highly useful advice from working researchers. After I introduced myself, one student contacted me to ask how I found my current research topic. The problem of finding a good research problem is something I never quite understood myself, so I was happy to describe the long and sometimes confused story of how I ended up working on my current work.


Later I had the good fortune to notice that another student was a good fit for the [Frost Scholarship](https://www.scholarshipdesk.com/frost-scholarship-programme-florida-at-oxford-university/), a wonderful program that is not as well-known as comparable ones. I mostly know about the award because I happen to be among the first students to receive it, so I introduced myself more personally and described the nature of the award and its merits. It is precisely these kinds of chance encounters that make conferences so valuable. In fact, when I later asked an unrelated question to [Simon Peyton Jones](https://www.microsoft.com/en-us/research/people/simonpj/), he emphasized that the course of an academic career is highly non-deterministic and easily affected by random incidents such as the one just described. The takeaway is this: In an academic (or related) career, you simply cannot know in advance which moments will most affect your overall trajectory. So take every opportunity you can get, keep an open mind, and meet people! This is part of what PLMW is for.

## The presentations

The workshop was divided into a few speaker sessions, with time in between for chatting with other attendees. The talks varied in content, some emphasizing technical topics, others focusing on more general career advice.

The first session kicked off with a general "Welcome" talk by the organizers. After that we had the pleasure of [Derek Dreyer](https://people.mpi-sws.org/~dreyer/) teaching us how to write a readable paper. Many in the audience agreed that a non-trivial fraction of research papers are hard to read simply because they are not written well. I found this talk exciting because several weeks ago, by coincidence, a reading group at Penn read part of Dreyer's PhD dissertation and agreed that it was a good example of clear writing. Hearing directly from researchers whose work you admire is an exciting, but sometimes intimidating, part of the conference experience.

After a half-hour break spent socializing, we had a second session of three 40-minute talks. Two of the presentations were technical, focusing on constraints solvers and operational semantics. They covered material I mostly understood already, but they were enjoyable nonetheless. I would have found it useful to attend a couple years ago, particularly to learn about operational semantics. Instead, I was able to offer some advice to newer students, namely that the subtlety of the topic is hard to appreciate until you start trying to prove theorems about real languages. I think most students would have found the talks useful, even without much background in the respective subjects, if only to get some exposure to the basic ideas.

The third talk of this session was the one I was most interested in, titled "Managing your Research, your Advisor, your PhD." The main idea was that completing a PhD is a responsibility falling largely on *your* shoulders and not your advisor's. *You* must be the one to balance your time, keep track of your research projects, initiate meetings (sometimes), and generally dedicate yourself to furthering your education. Students should therefore try to learn and apply these skills as soon as possible. This requires advice and practice, so I was grateful for the presentation.

Following the second session we had some unstructured time to eat lunch and meet other attendees. For this, CLOWDR provides users with the ability to create temporary "chat rooms" where you can talk to other attendees over Zoom. I joined a room that had some friends of mine in it, where I also met a handful of other students from around the world. I was able to offer some advice to undergraduates thinking about grad school, particularly on the topic of whether it is worthwhile to pursue a master's degree (MS) before a PhD. (The answer I gave is that it can be worthwhile to pursue a European MS if it comes with funding, as these programs are often designed to prepare students for more advanced studies. American MS programs are often "terminal" degrees that you pay for, and they're not always stepping stones to PhDs in STEM fields in my experience. But this might depend on the exact MS program you have in mind.)

The third session consisted of two 45-minute talks. First, [Kenny Foner](https://very.science/) gave a presentation titled, "How Can I Academia When My Brain Can't Even? Mental Health in Grad School and Beyond." My impression was that this talk generated the most discussion and excitement at PLMW this year. I'm not sure how well I can capture the emotional impact of the talk, but fortunately Kenny has given it many times and a video from POPL is available [here on Youtube](https://www.youtube.com/watch?v=Mi2dMiGSu_4). The message, in short, is as follows: Doing a PhD is very stressful, and many academics will experience at least some symptoms of depression or anxiety in the course of their careers. Your mental health is something to take seriously, and all of us should understand the resources available to us, as well as resist internalizing or propagating the stigmas that can surround this topic. When things feel overwhelming, don't hesitate to take some time off or seek help.

The second talk by [Nada Amin](https://namin.seas.harvard.edu/people/nada-amin) explained an interesting use of functional programming to explore graph-based databases, which evidently is useful for biomedical research. Of all of the talks, this was the one I benefited from most on a technical level. The talk presented many ideas and technical terms that I want to explore further, as applying PL theory to data management is a topic I find compelling. As I look more into the research presented, I would not be surprised to find some inspiration for my own research on [Datalog](https://en.wikipedia.org/wiki/Datalog).

To finish the workshop, our final session was a panel discussion with a variety of researchers drawn from industry and academia. It was only scheduled for an hour, but a few panelists stayed much longer to answer questions from an eager audience. Students earlier in their careers asked how to be choose a graduate school, how to find a job, and how to write good applications, among other things. Later students asked questions about the publication process, knowing if a research area is going to produce novel results, and how to decide between careers in industry and academia.

I couldn't do a good job summarizing the advice the panel gave us, except for one question that I asked: "Does the exact topic of my PhD dissertation determine the fate of my academic career?" My expectation was that many researchers work on topics that are not directly related to their PhD work, and that's generally what the panel told us. This is also when Simon Peyton Jones mentioned that an academic career can be quite hard to predict, as chance opportunities often play a big role in one's career (hence the benefit of attending conferences). The panel mentioned that a postdoctoral position can be desirable if you intend to pivot or adjust your research focus, as these can be "transitional" positions. It's harder to shift focus if you go straight into a junior professor position, where you are immediately hit with many obligations and might not have enough experience to risk trying to enter a new subfield.

Another audience member commented that it was quite stress-relieving to hear such distinguished panel members talk about their rough experiences: rejection, stress, the ever-present sensation that you're not actually as smart as the people around you, etc. Other agreed with this sentiment, including me. While you can find some good advice online about graduate school, I don't think there's a good substitute for personal interactions like this panel. Of course, even better would be in-person conferences where you can interact more personally and even hang out after the conference at a local venue. Still, CLOWDR did a pretty good job at simulating a physical conference, and this will probably become more true with time and feedback.

# Conclusion

PLMW 2020 was a fantastic experience that I would recommend to anyone. The organizers did a great job, and the atmosphere was at all times respectful, encouraging, and engaging. Attendees benefited to hear from real experts in their fields, as well as other students at different points in their careers. To the greatest extent possible, Clowdr did a commendable job creating the illusion of a physical conference with all its random encounters with other students and researchers. The talks and the speakers were diverse and well-selected in several respects, presenting a good picture of what the PL community is like. From talking to other students, my sense is that attendees walked away from PLMW 2020 with a greater understanding and excitement for programming language research. I know I did.
