"""
Script to convert .csv files of PL club people to individual .md files.

This was used to generate the current data in /people.

# Expected input

- student.csv, faculty.csv, postdoc.csv

  These files should have 3 columns.

- alum.csv

  This file should have 5 columns.

# Expected output

- In the 'people' subdirectory, a separate file 'Name.md" for each person, containing fields with the relevant info about that person.

## Example input (student.csv, faculty.csv, and postdoc.csv):

Benjamin Pierce,https://www.cis.upenn.edu/~bcpierce/,bcpierce
Stephanie Weirich,https://www.cis.upenn.edu/~sweirich/,swericih
Steve Zdancewic,https://www.cis.upenn.edu/~stevez/,stevez
Rajeev Alur,https://www.cis.upenn.edu/~alur/,alur
Mayur Naik,https://www.cis.upenn.edu/~mhnaik/,mhnaik
Osbert Bastani,https://obastani.github.io/,obastani

## Example input (alum.csv):

Kihong Heo ,Postdoc,2019,KAIST,https://www.cis.upenn.edu/~kheo/
Mukund Raghothaman,Postdoc,2019,USC,https://r-mukund.github.io/
Joachim Breitner,Postdoc,2019,DFINITY,https://www.joachim-breitner.de/blog
Brian Heath,Masters,2019,Tortuga,http://brianheath.info/

"""


import csv

curr = ['student', 'faculty', 'postdoc']
for group in curr:
    with open(group + '.csv') as csvfile:
        reader = csv.reader(csvfile, delimiter=',')
        for row in reader:
            ident = row[0].split(" ")[0] + row[0].split(" ")[1][0]
            f = open("../people/" + ident + ".md","w+")
            f.write("---\n")
            f.write("name : \"" + row[0].strip() + "\"\n")
            f.write("website : \"" + row[1].strip() + "\"\n")
            f.write("email : \"" + row[2].strip() + "@seas.upenn.edu\"\n")
            f.write("tags : [\"" + group + "\"]\n")
            f.write("headshot : \"" + ident + ".jpg\"\n")
            f.write("---\n")

with open('alum.csv') as csvfile:
    reader = csv.reader(csvfile, delimiter=',')
    for row in reader:
        ident = row[0].split(" ")[0] + row[0].split(" ")[1][0]
        f = open("../people/" + ident + ".md","w+")
        f.write("---\n")
        f.write("name : \"" + row[0].strip() + "\"\n")
        f.write("degree : \"" + row[1].strip() + "\"\n")
        f.write("year : \"" + row[2].strip() + "\"\n")
        f.write("where : \"" + row[3].strip() + "\"\n")
        f.write("website : \"" + row[4].strip() + "\"\n")
        f.write("tags : [\"alum\"]\n")
        f.write("---\n")
