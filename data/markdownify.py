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