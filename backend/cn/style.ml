let style =
  "\n\
   * {\n\
  \    font-size: 11pt\n\
   }\n\n\
   html {\n\
  \    font-family: sans-serif;\n\
  \    padding: 0;\n\
  \    margin: 0;\n\
  \    /* font-size: 8pt; */\n\
   }\n\n\
   body {\n\
  \    padding-left: 10px;\n\
  \    padding-right: 10px;\n\
  \    padding-bottom: 10px;\n\
  \    margin: 0;\n\
  \    max-width: 800px;\n\
   }\n\n\
   table {\n\
  \    width: 100%;\n\
  \    border: 1px solid;\n\
  \    border-collapse: collapse;\n\
  \    /* max-width: 1400px; */\n\
  \    /* table-layout: fixed; */\n\
   }\n\n\
   h1 {\n\
  \    font-size: 11pt;\n\
  \    margin-top: 16pt;\n\
   }\n\n\
   tr {\n\
  \    padding : 0;\n\
  \    margin : 0;\n\
   }\n\n\
   th, td {\n\
  \    text-align: left;\n\
  \    vertical-align: top;\n\
  \    border-left: 1px solid;\n\
  \    border-right: 1px solid;\n\
  \    padding-left: 5px;\n\
  \    padding-right: 5px;\n\
  \    padding-top: 3px;\n\
  \    padding-bottom: 3px;\n\
   }\n\n\
   th {\n\
  \    padding-top: 5px;\n\
  \    padding-bottom: 5px;\n\
   }\n\n\
   th {\n\
  \    font-weight: normal;\n\
  \    font-style: italic;\n\
   }\n\n\
   .pagelinks {\n\
  \    padding-top: 10px;\n\
  \    padding-bottom: 30px;\n\
   }\n\n\
   #pages .page { display: none }\n\
   #pages .page:target { display: block }\n\n\
   #pages .pagelinks .button,\n\
   #pages .pagelinks .inactive_button {\n\
  \  padding-top: 5px;\n\
  \  padding-bottom: 5px;\n\
  \  padding-left: 10px;\n\
  \  padding-right: 10px;\n\
  \  display: inline-block;\n\
   }\n\n\n\n\
   @media (prefers-color-scheme: dark) {\n\n\
  \    html {\n\
  \        background-color: black;\n\
  \        color: lightgray;\n\
  \    }\n\n\
  \    table, th, td {\n\
  \        border-color: #303030;\n\
  \    }\n\n\
  \    tr {\n\
  \        background-color: #181818;\n\
  \    }\n\n\
  \    th {\n\
  \        background-color: #252525;\n\
  \        border-bottom: 1px solid #303030;\n\
  \    }\n\n\
  \    tr:hover {\n\
  \        background-color: #101044;\n\
  \    }\n\n\
  \    #pages .pagelinks .button,\n\
  \    #pages .pagelinks .inactive_button {\n\
  \        background-color: white;\n\
  \        border: 1px solid #EEEEEE;\n\
  \    }\n\n\
  \    #pages .pagelinks .button:hover {\n\
  \        background-color: #BBBBBB;\n\
  \    }\n\n\
  \    #pages .pagelinks .button a {\n\
  \        color: black;\n\
  \        text-decoration: none;\n\
  \    }\n\n\
  \    .pagelinks .inactive_button {\n\
  \        color: #AAAAAA;\n\
  \    }\n\n\
   }\n\n\n\n\
   @media (prefers-color-scheme: light) {\n\n\
  \    html {\n\
  \        background-color: white;\n\
  \        color: black;\n\
  \    }\n\n\
  \    table, th, td {\n\
  \        border-color: #E9E9E9;\n\
  \    }\n\n\
  \    tr {\n\
  \        background-color: #F8F8F8;\n\
  \    }\n\n\
  \    th {\n\
  \        background-color: #F0F0F0;\n\
  \        border-bottom: 1px solid #E9E9E9;\n\
  \    }\n\n\
  \    tr:hover {\n\
  \        background-color: #E2F0FF;\n\
  \    }\n\n\
  \    #pages .pagelinks .button,\n\
  \    #pages .pagelinks .inactive_button {\n\
  \        background-color: black;\n\
  \        border: 1px solid #111111;\n\
  \    }\n\n\
  \    #pages .pagelinks .button:hover {\n\
  \        background-color: #444444;\n\
  \    }\n\n\
  \    #pages .pagelinks .button a {\n\
  \        color: white;\n\
  \        text-decoration: none;\n\
  \    }\n\n\
  \    .pagelinks .inactive_button {\n\
  \        color: #555555;\n\
  \    }\n\
   }\n"
